import PlanarHom.OccurrencePfaffianProgramBridge
import PlanarHom.OccurrencePfaffianStateBounds
import PlanarHom.PfaffianEliminationHeights

/-! NEW reconstruction. The original-input minor certificate is initialized and
preserved along every actual list-machine step. -/
namespace PlanarHom.PfaffianList
open Complexity MultiGraph.PfaffianElimination
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {n dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def MatrixState (A : Matrix (Fin n) (Fin n) K) (s : State K) : Prop :=
  ∃ (B : Matrix (Fin n) (Fin n) K) (active : List (Fin n)),
    s.1 = matrixRows B ∧ s.2.1 = active.map Fin.val ∧
      ValidState B active ∧ SchurState A B active

 theorem matrixState_initial (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    MatrixState A (initialState (matrixRows A)) := by
  refine ⟨A, List.finRange n, rfl, ?_, ⟨hskew,hdiag,List.nodup_finRange n⟩,
    schurState_initial A _⟩
  simp [initialState]

 theorem matrixState_step (A : Matrix (Fin n) (Fin n) K) (s : State K)
    (hs : MatrixState A s) : MatrixState A (step s) := by
  rcases s with ⟨g,xs,a⟩
  rcases hs with ⟨B,active,hg,hx,hvalid,hschur⟩
  dsimp only at hg hx
  subst g
  subst xs
  cases active with
  | nil => simpa using (show MatrixState A (matrixRows B,([],a)) from
      ⟨B,[],rfl,rfl,hvalid,hschur⟩)
  | cons i xs =>
    cases hp : firstPivot B i xs with
    | none =>
      rw [step_matrixRows_noPivot B i xs a hp]
      refine ⟨B,[],rfl,rfl,⟨hvalid.1,hvalid.2.1,by simp⟩,?_⟩
      rcases hschur with ⟨I,fI,dI,p,hinj,_,hdet,hB⟩
      exact ⟨I,fI,dI,p,hinj,by simp,hdet,hB⟩
    | some q =>
      rcases q with ⟨k,j⟩
      rw [step_matrixRows_pivot B i xs a hp]
      exact ⟨pivotUpdate B i j,xs.eraseIdx k,rfl,rfl,
        validState_update B i xs k j hvalid,schurState_pivot A B i xs hschur hvalid hp⟩

 theorem matrixState_iterate (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) (t : ℕ) :
    MatrixState A (step^[t] (initialState (matrixRows A))) := by
  induction t with
  | zero => exact matrixState_initial A hskew hdiag
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact matrixState_step A _ ih

 theorem stepFactor_scalar_independent (g : Grid K) (xs : List ℕ) (a b : K) :
    stepFactor (g,(xs,a)) = stepFactor (g,(xs,b)) := rfl

 theorem stepFactor_matrixRows_pivot (B : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (xs : List (Fin n)) (a : K) {k : ℕ} {j : Fin n}
    (hp : firstPivot B i xs = some (k,j)) :
    stepFactor (matrixRows B,((i::xs).map Fin.val,a)) = (-1:K)^k * B i j := by
  rw [stepFactor_scalar_independent _ _ a 1]
  have h := congrArg (fun s : State K => s.2.2) (step_matrixRows_pivot B i xs 1 hp)
  dsimp only at h
  rw [step_accumulator] at h
  simpa using h

 theorem stepFactor_matrixRows_noPivot (B : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (xs : List (Fin n)) (a : K) (hp : firstPivot B i xs = none) :
    stepFactor (matrixRows B,((i::xs).map Fin.val,a)) = 0 := by
  rw [stepFactor_scalar_independent _ _ a 1]
  have h := congrArg (fun s : State K => s.2.2) (step_matrixRows_noPivot B i xs 1 hp)
  dsimp only at h
  rw [step_accumulator] at h
  simpa using h

 theorem exists_factor_encoding_polynomial :
    ∃ p : Polynomial ℕ, ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (s : State K),
      MatrixState A s → ((numberFieldEncoding basis).encode (stepFactor s)).length ≤
        p.eval (PfaffianMinorHeights.matrixInputLength basis A) := by
  obtain ⟨q,hq⟩ := exists_polynomial_schur_entry_bound basis
  obtain ⟨negBody⟩ := FixedFieldArithmetic.fp_negation basis
  let e := numberFieldEncoding basis
  let z := (e.encode (0:K)).length + (e.encode (1:K)).length
  let r := MachineComposition.outputLengthPolynomial negBody
  let p := q + r.comp q + Polynomial.C z
  refine ⟨p, fun A s hs => ?_⟩
  rcases s with ⟨g,xs,a⟩
  rcases hs with ⟨B,active,hg,hx,hvalid,hschur⟩
  dsimp only at hg hx
  subst g
  subst xs
  have hb (i j) := hq A B active hschur i j
  have hneg (i j) : (e.encode (-B i j)).length ≤
      r.eval (q.eval (PfaffianMinorHeights.matrixInputLength basis A)) :=
    (MachineComposition.encoded_output_length_le negBody (B i j)).trans
      (MachineComposition.natPolynomial_monotone r (hb i j))
  simp only [p, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_C]
  cases active with
  | nil => simp only [List.map_nil, stepFactor, ↓reduceIte]; change (e.encode (1:K)).length ≤ _ + _ + z; dsimp only [z]; omega
  | cons i xs =>
    cases hp : firstPivot B i xs with
    | none =>
      rw [stepFactor_matrixRows_noPivot B i xs a hp]
      change (e.encode 0).length ≤ _ + _ + z
      omega
    | some v =>
      rcases v with ⟨k,j⟩
      rw [stepFactor_matrixRows_pivot B i xs a hp, neg_one_pow_eq_ite]
      split_ifs <;> simp only [one_mul, neg_one_mul]
      · exact (hb i j).trans (by omega)
      · exact (hneg i j).trans (by omega)

end PlanarHom.PfaffianList
