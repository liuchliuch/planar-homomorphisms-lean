import PlanarHom.SignedRankOneAlgebra
import PlanarHom.ThreeStateConnectedStar

/-! Exact support and signed-star transport for irreducible three-state
matrices. These results bridge the unsigned structural gate by actual entry
identities; they do not infer a signed classification from a nonnegative one. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open ThreeStateDimension

def PermutedStar (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃a b:ℝ,∃e:Equiv.Perm (Fin 3),∀i j,M i j=starMatrix a b (e i) (e j)

theorem noBooleanZeroCut_square_iff (M : Matrix (Fin 3) (Fin 3) ℝ) :
    NoBooleanZeroCut (schurSquare M) ↔ NoBooleanZeroCut M := by
  constructor <;> intro h f hf
  · apply h f
    intro i j hij
    simp [schurSquare,hf i j hij]
  · apply h f
    intro i j hij
    exact sq_eq_zero_iff.mp (hf i j hij)

theorem exists_row_nonzero_of_no_cut (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,M i j=M j i) (hc : NoBooleanZeroCut M) (i : Fin 3) :
    ∃j,M i j≠0 := by
  by_contra h
  push_neg at h
  let f : Fin 3→Bool := fun j=>decide (j=i)
  have hz : ∀x y,f x≠f y→M x y=0 := by
    intro x y hxy
    by_cases hx : x=i
    · subst x
      exact h y
    by_cases hy : y=i
    · subst y
      rw [hs x i]
      exact h x
    · exact False.elim (hxy (by simp [f,hx,hy]))
  obtain ⟨j,hj⟩ := exists_ne i
  have hh := hc f hz i j
  simp [f,hj] at hh

theorem rank_one_no_cut_full_support (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,M i j=M j i) (hc : NoBooleanZeroCut M) (hr : M.rank≤1) :
    ∀i j,M i j≠0 := by
  have hrow := exists_row_nonzero_of_no_cut M hs hc
  rcases scalar_outer_of_rank_le_one M hs hr with hz|⟨p,hp,hm⟩
  · obtain ⟨j,hj⟩ := hrow 0
    exact False.elim (hj (by simp [hz]))
  · have he (i j : Fin 3) : M i j=(M p p)⁻¹*(M i p*M j p) :=
      congrFun (congrFun hm i) j
    have hn (i : Fin 3) : M i p≠0 := by
      intro h
      obtain ⟨j,hj⟩ := hrow i
      exact hj (by rw [he i j,h,zero_mul,mul_zero])
    intro i j
    rw [he]
    exact mul_ne_zero (inv_ne_zero hp) (mul_ne_zero (hn i) (hn j))

/-- Taking real square roots is unnecessary: the zero support positions of
a squared star already force the original signed star. -/
theorem star_of_squared_star (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,M i j=M j i) (a b : ℝ)
    (hm : ∀i j,schurSquare M i j=starMatrix a b i j) :
    ∀i j,M i j=starMatrix (M 0 2) (M 1 2) i j := by
  intro i j
  have h := hm i j
  fin_cases i <;> fin_cases j <;> simp [starMatrix,schurSquare] at h ⊢
  all_goals first | exact h | exact sq_eq_zero_iff.mp h | exact hs _ _

theorem permutedStar_of_squared_permutedStar (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,M i j=M j i) (h : PermutedStar (schurSquare M)) : PermutedStar M := by
  obtain ⟨a,b,e,h⟩ := h
  let N : Matrix (Fin 3) (Fin 3) ℝ := fun i j=>M (e.symm i) (e.symm j)
  have hN : ∀i j,schurSquare N i j=starMatrix a b i j := by
    intro i j
    simpa only [e.apply_symm_apply] using h (e.symm i) (e.symm j)
  have ht := star_of_squared_star N (fun i j=>hs _ _) a b hN
  refine ⟨N 0 2,N 1 2,e,?_⟩
  intro i j
  simpa only [N,e.symm_apply_apply] using ht (e i) (e j)

end PlanarHom.SignedThreeState
