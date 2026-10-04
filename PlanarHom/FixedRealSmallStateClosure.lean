import PlanarHom.FixedRealHadamard
import PlanarHom.FixedRealBipartiteEvaluation
import PlanarHom.SignedBlockTractability

/-! NEW represented closure for signed small-state easy families. Every
closure constructs actual code programs. The singleton scalar is unrestricted. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSmallState
open DensePolynomial FixedRealGraphEvaluation SignedThreeState
variable {n e : ℕ} {K C D : Type} [Field K] [Algebra (RationalFunction n) K]
variable [Fintype C] [Fintype D]
local instance (priority := 10000) smallStateBoolDecEq : DecidableEq Bool := Classical.decEq Bool
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

 theorem finite_rankOne (a : C → K) : Evaluable basis (fun i j => a i * a j) (fun _ => 1) := by
  let p := Fintype.equivFin C
  have h := color basis p (fun i j => a (p.symm i) * a (p.symm j)) (fun _ => 1)
    (rankOne basis (fun i => a (p.symm i)) (fun _ => 1))
  simpa only [p.symm_apply_apply] using h

 theorem scalar_rankOne (γ : K) (a : C → K) :
    Evaluable basis (γ • (fun i j => a i * a j)) (fun _ => 1) :=
  scalar basis γ _ (finite_rankOne basis a)

 theorem real_rankOne (φ : K →+* ℝ) (M : Matrix C C K)
    (hs : ∀i j, M i j = M j i) (hr : Matrix.rank (fun i j => φ (M i j)) ≤ 1) :
    Evaluable basis M (fun _ => 1) := by
  rcases scalar_outer_of_rank_le_one (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j)) hr with hz | ⟨p,hp,hm⟩
  · have hzero : M = 0 := by ext i j; apply φ.injective; simpa using congrFun (congrFun hz i) j
    have he : M = (0 : K) • (fun i j : C => (1 : K) * 1) := by simp [hzero]
    rw [he]
    exact scalar_rankOne basis 0 (fun _ => 1)
  · have hminor : ∀i j, M i j * M p p = M i p * M p j := by
      intro i j
      apply φ.injective
      simpa only [map_mul] using minor_eq_zero_of_rank_le_one (fun i j => φ (M i j)) hr i p j p
    have he := scalar_outer_of_pivot M p ((map_ne_zero φ).mp hp) hs hminor
    rw [he]
    exact scalar_rankOne basis _ _

 theorem directSum (A : Matrix C C K) (B : Matrix D D K)
    (hsA : ∀i j, A i j = A j i) (hsB : ∀i j, B i j = B j i)
    (hA : Evaluable basis A (fun _ => 1)) (hB : Evaluable basis B (fun _ => 1)) :
    Evaluable basis (Matrix.fromBlocks A 0 0 B) (fun _ => 1) := by
  refine fibers basis Sum.isRight _ ?_ ?_ (fun _ => 1) ?_
  · intro i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,hsA,hsB]
  · intro i j h
    cases i <;> cases j <;> simp_all [Matrix.fromBlocks]
  · intro b
    cases b
    · have hm : (fun i j : {x : C ⊕ D // x.isRight = false} =>
          (Matrix.fromBlocks A 0 0 B) i.val j.val) =
          (fun i j => A (leftSumFiber i) (leftSumFiber j)) := by
        funext ⟨i,hi⟩ ⟨j,hj⟩
        cases i with
        | inl i => cases j with
          | inl j => rfl
          | inr j => exact Bool.noConfusion hj
        | inr i => exact Bool.noConfusion hi
      rw [hm]
      exact color basis leftSumFiber A (fun _ => 1) hA
    · have hm : (fun i j : {x : C ⊕ D // x.isRight = true} =>
          (Matrix.fromBlocks A 0 0 B) i.val j.val) =
          (fun i j => B (rightSumFiber i) (rightSumFiber j)) := by
        funext ⟨i,hi⟩ ⟨j,hj⟩
        cases i with
        | inl i => exact Bool.noConfusion hi
        | inr i => cases j with
          | inl j => exact Bool.noConfusion hj
          | inr j => rfl
      rw [hm]
      exact color basis rightSumFiber B (fun _ => 1) hB

 theorem singleton (t : K) : Evaluable basis (fun _ _ : Fin 1 => t) (fun _ => 1) := by
  have he : (fun _ _ : Fin 1 => t) = t • (fun _ _ : Fin 1 => (1 : K) * 1) := by ext i j; simp
  rw [he]
  exact scalar_rankOne basis t (fun _ => 1)

 theorem diagonal_boolean (a c : K) : Evaluable basis (booleanBool a 0 c) (fun _ => 1) := by
  have h := directSum basis (fun _ _ : Fin 1 => a) (fun _ _ : Fin 1 => c)
    (fun _ _ => rfl) (fun _ _ => rfl) (singleton basis a) (singleton basis c)
  have hm : booleanBool a 0 c = fun i j =>
      (Matrix.fromBlocks (fun _ _ : Fin 1 => a) 0 0 (fun _ _ : Fin 1 => c)) (boolSumOne i) (boolSumOne j) := by
    funext i j; cases i <;> cases j <;> rfl
  rw [hm]
  exact color basis boolSumOne _ (fun _ => 1) h

 theorem rankOne_boolean (a b c : K) (h : a * c = b ^ 2) :
    Evaluable basis (booleanBool a b c) (fun _ => 1) := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := sq_eq_zero_iff.mp (by simpa using h.symm)
    subst b
    exact diagonal_boolean basis 0 c
  have hm : booleanBool a b c = a⁻¹ • (fun i j : Bool => (if i then b else a) * (if j then b else a)) := by
    funext i j
    cases i <;> cases j <;> simp [booleanBool,Pi.smul_apply,smul_eq_mul]
    · field_simp
    · field_simp
    · field_simp
    · apply mul_left_cancel₀ ha
      rw [←mul_assoc,mul_inv_cancel₀ ha,one_mul]
      simpa [pow_two] using h
  rw [hm]
  exact scalar_rankOne basis _ _

 theorem two_plus_one (a b c t : K) (h : Evaluable basis (booleanBool a b c) (fun _ => 1)) :
    Evaluable basis (blockMatrix a b c t) (fun _ => 1) := by
  have hf := color basis finTwoEquiv (booleanBool a b c) (fun _ => 1) h
  have hm : (fun i j => booleanBool a b c (finTwoEquiv i)
      (finTwoEquiv j)) = booleanMatrix a b c := by
    funext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hm] at hf
  have hb := directSum basis (booleanMatrix a b c) (fun _ _ : Fin 1 => t)
    (by intro i j; fin_cases i <;> fin_cases j <;> rfl) (fun _ _ => rfl) hf (singleton basis t)
  have hm' : blockMatrix a b c t = fun i j =>
      (Matrix.fromBlocks (booleanMatrix a b c) 0 0 (fun _ _ : Fin 1 => t)) (threeStarColors i) (threeStarColors j) := by
    funext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hm']
  exact color basis threeStarColors _ (fun _ => 1) hb

 theorem signed_star (a b : K) : Evaluable basis (starMatrix a b) (fun _ => 1) := by
  have h := bipartite basis (![a,b]) (fun _ => 1) (fun _ : Fin 1 => 1) (fun _ => 1)
  have hw : Sum.elim (fun _ : Fin 2 => (1 : K)) (fun _ : Fin 1 => 1) = fun _ => 1 := by
    funext i; cases i <;> rfl
  rw [hw] at h
  have hm : starMatrix a b = fun i j => BipartiteRankTwoTractability.matrix
      (![a,b]) (fun _ : Fin 1 => 1) (threeStarColors i) (threeStarColors j) := by
    funext i j; fin_cases i <;> fin_cases j <;> simp [starMatrix,threeStarColors,BipartiteRankTwoTractability.matrix]
  rw [hm]
  exact color basis threeStarColors _ (fun _ => 1) h

end PlanarHom.FixedRealSmallState
