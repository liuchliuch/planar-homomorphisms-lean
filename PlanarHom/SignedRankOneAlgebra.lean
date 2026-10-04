import PlanarHom.SignedThreeStateAlgebra
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Signed symmetric rank-one factorization in the source field, with no
positive-semidefinite hypothesis and no square-root extension. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
variable {F n : Type} [Field F] [Fintype n]

theorem submatrix_rank_le (M : Matrix n n F) (r c : Fin 2→n) :
    (M.submatrix r c).rank ≤ M.rank := by
  rw [←Matrix.cRank_toNat_eq_rank,←Matrix.cRank_toNat_eq_rank]
  apply Cardinal.toNat_le_toNat (Matrix.cRank_submatrix_le M r c)
  exact lt_of_le_of_lt (Matrix.cRank_le_card_width M) (Cardinal.nat_lt_aleph0 _)

theorem minor_eq_zero_of_rank_le_one (M : Matrix n n F) (hr : M.rank≤1)
    (i j k l : n) : M i k*M j l=M i l*M j k := by
  let A := M.submatrix (![i,j] : Fin 2→n) (![k,l] : Fin 2→n)
  have hA : A.rank≤1 := (submatrix_rank_le M _ _).trans hr
  have hd : A.det=0 := by
    by_contra hn
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
    have he := Matrix.rank_of_isUnit A hu
    simp only [Fintype.card_fin] at he
    omega
  have he : A.det = M i k*M j l-M i l*M j k := by
    simp [A,Matrix.det_fin_two,Matrix.submatrix_apply]
  exact sub_eq_zero.mp (he.symm.trans hd)

/-- A nonzero symmetric rank-one matrix has a nonzero diagonal, in arbitrary
characteristic. Both positive and negative real scalar pivots are preserved. -/
theorem exists_diagonal_ne_zero_of_rank_le_one (M : Matrix n n F)
    (hs : ∀i j,M i j=M j i) (hr : M.rank≤1) (hne : M≠0) :
    ∃p,M p p≠0 := by
  by_contra h
  push_neg at h
  apply hne
  funext i j
  have hm := minor_eq_zero_of_rank_le_one M hr i j i j
  rw [h i,h j,zero_mul,hs j i] at hm
  exact (mul_self_eq_zero.mp hm.symm)

/-- Exact algebraic source-field description of every symmetric rank≤1 case.
The zero matrix is explicit; every other case has a signed scalar outer product. -/
theorem scalar_outer_of_rank_le_one (M : Matrix n n F)
    (hs : ∀i j,M i j=M j i) (hr : M.rank≤1) :
    M=0 ∨ ∃p,M p p≠0 ∧ M=(M p p)⁻¹ • (fun i j=>M i p*M j p) := by
  by_cases hz : M=0
  · exact Or.inl hz
  · obtain ⟨p,hp⟩ := exists_diagonal_ne_zero_of_rank_le_one M hs hr hz
    exact Or.inr ⟨p,hp,scalar_outer_of_pivot M p hp hs
      (fun i j=>minor_eq_zero_of_rank_le_one M hr i p j p)⟩

end PlanarHom.SignedThreeState
