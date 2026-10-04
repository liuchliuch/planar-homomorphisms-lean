import PlanarHom.PfaffianSchurMinors

/-!
# Original-input minor certificates along actual Pfaffian elimination

The invariant is initialized and preserved by the actual first-pivot transition.
Its principal block is a selected submatrix of the original input, not an
unconstrained family of hypothetical bounded quantities.
-/
noncomputable section
open scoped Matrix
namespace PlanarHom.MultiGraph.PfaffianElimination
open Matrix
variable {F : Type} [Field F] {n : ℕ}

/-- An exact original-input Schur certificate; selected vertices have been removed
from the current active list. -/
def SchurState (A B : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (p : I → Fin n),
    Function.Injective p ∧ (∀ t, p t ∉ active) ∧
      (A.submatrix p p).det ≠ 0 ∧ B = schurResidual A p

/-- Every actual input begins with the empty processed principal minor. -/
theorem schurState_initial (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) :
    SchurState A A active := by
  refine ⟨Fin 0, inferInstance, inferInstance, Fin.elim0, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · simp
  · exact (schurResidual_empty A _).symm

/-- A nonzero actual pivot extends the original-input principal minor by its
actual two distinct vertices, and preserves the precise Schur representation. -/
theorem schurState_pivot [DecidableEq F] (A B : Matrix (Fin n) (Fin n) F)
    (i : Fin n) (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (hstate : SchurState A B (i :: xs)) (hvalid : ValidState B (i :: xs))
    (hpivot : firstPivot B i xs = some (k,j)) :
    SchurState A (pivotUpdate B i j) (xs.eraseIdx k) := by
  rcases hstate with ⟨I, fI, dI, p, hinj, hdis, hdet, hB⟩
  letI := fI
  letI := dI
  letI : Invertible (A.submatrix p p) := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet)
  have hp := firstPivot_nonzero B i xs hpivot
  have hget := (firstPivot_some_spec B i xs hpivot).2.1
  have hj : j ∈ xs := List.mem_of_getElem? hget
  have hij : i ≠ j := by
    intro he
    exact hvalid.2.2.notMem (he ▸ hj)
  have hqdet : (B.submatrix ![i,j] ![i,j]).det ≠ 0 := by
    rw [pivot_principal_det B i j hvalid.1 hvalid.2.1]
    exact pow_ne_zero _ hp
  letI : Invertible ((schurResidual A p).submatrix ![i,j] ![i,j]) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (hB ▸ hqdet))
  have hnewdet : (A.submatrix (Sum.elim p ![i,j]) (Sum.elim p ![i,j])).det ≠ 0 :=
    schurResidual_extend_det_ne_zero A p ![i,j] (hB ▸ hqdet)
  have hji : j ∉ xs.eraseIdx k := by
    intro hm
    have ht := List.mem_toFinset.mpr hm
    rw [nodup_eraseIdx_toFinset xs hvalid.2.2.tail hget] at ht
    exact (Finset.mem_erase.mp ht).1 rfl
  have hii : i ∉ xs.eraseIdx k := fun hm => hvalid.2.2.notMem (List.mem_of_mem_eraseIdx hm)
  have hpi (t : I) : p t ≠ i := by
    intro he
    exact hdis t (by simp [he])
  have hpj (t : I) : p t ≠ j := by
    intro he
    exact hdis t (by simp [he, hj])
  refine ⟨I ⊕ Fin 2, inferInstance, inferInstance, Sum.elim p ![i,j], ?_, ?_, hnewdet, ?_⟩
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hinj hab)
      | inr b =>
        exfalso
        fin_cases b
        · exact hpi a hab
        · exact hpj a hab
    | inr a =>
      cases b with
      | inl b =>
        exfalso
        fin_cases a
        · exact hpi b hab.symm
        · exact hpj b hab.symm
      | inr b => fin_cases a <;> fin_cases b <;> simp_all
  · intro t
    cases t with
    | inl t =>
      intro ht
      exact hdis t (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx ht))
    | inr t =>
      fin_cases t
      · simpa using hii
      · simpa using hji
  · rw [schurResidual_extend, ← hB, schurResidual_pair B i j hvalid.1 hvalid.2.1 hp]
    rfl

section NumberField
variable [Algebra ℚ F] {dimension : ℕ}
open Complexity PfaffianMinorHeights

/-- One uniform polynomial bounds every matrix entry in every initialized and
preserved Schur state, in the original matrix's actual nested-list input bits. -/
theorem exists_polynomial_schur_entry_bound (basis : Module.Basis (Fin dimension) ℚ F) :
    ∃ q : Polynomial ℕ, ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) (active : List (Fin n)),
      SchurState A B active → ∀ u v,
      ((numberFieldEncoding basis).encode (B u v)).length ≤ q.eval (matrixInputLength basis A) := by
  obtain ⟨q,hq⟩ := exists_polynomial_bordered_ratio_encoding_bound basis
  refine ⟨q, fun A B active hstate u v => ?_⟩
  rcases hstate with ⟨I, fI, dI, p, hinj, _, hdet, rfl⟩
  letI := fI
  letI := dI
  letI : Invertible (A.submatrix p p) := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet)
  rw [schurResidual_entry_minor]
  have hcard := Fintype.card_le_of_injective p hinj
  exact hq A (Sum.elim p (fun _ : Unit => u)) (Sum.elim p (fun _ : Unit => v)) p p
    (by simpa using Nat.add_le_add_right hcard 1) (by simpa using hcard.trans (Nat.le_succ _))

end NumberField
end PlanarHom.MultiGraph.PfaffianElimination
