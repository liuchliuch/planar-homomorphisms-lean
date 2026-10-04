import PlanarHom.SignedRankOneAlgebra
import PlanarHom.SupportTransformCompatibility

/-! The source sign transform gives a ±1 matrix. In dimension three its
squared Gram entries are strictly positive, and rank one of that transform
forces rank one of the sign matrix. No positivity of the original source is
assumed and no complexity theorem is used in this algebraic module. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SignedThreeState

def rowGram (S : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j=>∑k,S i k*S j k

theorem triple_units_sum_ne_zero (x y z : ℝ)
    (hx : x^2=1) (hy : y^2=1) (hz : z^2=1) : x+y+z≠0 := by
  rcases sq_eq_one_iff.mp hx with rfl|rfl <;>
  rcases sq_eq_one_iff.mp hy with rfl|rfl <;>
  rcases sq_eq_one_iff.mp hz with rfl|rfl <;> norm_num

theorem triple_units_extremal (x y z : ℝ)
    (hx : x^2=1) (hy : y^2=1) (hz : z^2=1)
    (h : (x+y+z)^2=9) : x=y ∧ x=z := by
  rcases sq_eq_one_iff.mp hx with rfl|rfl <;>
  rcases sq_eq_one_iff.mp hy with rfl|rfl <;>
  rcases sq_eq_one_iff.mp hz with rfl|rfl <;> norm_num at *

theorem rowGram_symmetric (S : Matrix (Fin 3) (Fin 3) ℝ) :
    ∀i j,rowGram S i j=rowGram S j i := by
  intro i j
  simp [rowGram,mul_comm]

theorem rowGram_diag (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : ∀i j,(S i j)^2=1) (i : Fin 3) : rowGram S i i=3 := by
  simp [rowGram,←pow_two,hS]

theorem schurSquare_rowGram_positive (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : ∀i j,(S i j)^2=1) : ∀i j,0<schurSquare (rowGram S) i j := by
  intro i j
  apply sq_pos_of_ne_zero
  simp only [rowGram,Fin.sum_univ_three]
  exact triple_units_sum_ne_zero _ _ _
    (by rw [mul_pow,hS,hS,one_mul]) (by rw [mul_pow,hS,hS,one_mul])
    (by rw [mul_pow,hS,hS,one_mul])

/-- Every pair of sign rows is proportional if the squared Gram has rank≤1. -/
theorem sign_row_products_of_squaredGram_rank_le_one
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : ∀i j,(S i j)^2=1)
    (hr : (schurSquare (rowGram S)).rank≤1) (i : Fin 3) :
    ∀j,S i j*S 0 j=S i 0*S 0 0 := by
  have hm := minor_eq_zero_of_rank_le_one (schurSquare (rowGram S)) hr i 0 i 0
  have hg : (rowGram S i 0)^2=9 := by
    simp only [schurSquare,rowGram_diag S hS,rowGram_symmetric S 0 i] at hm
    nlinarith [sq_nonneg (rowGram S i 0)]
  have hu (j : Fin 3) : (S i j*S 0 j)^2=1 := by rw [mul_pow,hS,hS,one_mul]
  rw [rowGram,Fin.sum_univ_three] at hg
  have he := triple_units_extremal _ _ _ (hu 0) (hu 1) (hu 2) hg
  intro j
  fin_cases j
  · rfl
  · exact he.1.symm
  · exact he.2.symm

/-- Entrywise squaring a three-row sign Gram cannot hide non-rank-one data. -/
theorem rank_le_one_of_squaredSignGram_rank_le_one
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : ∀i j,(S i j)^2=1)
    (hr : (schurSquare (rowGram S)).rank≤1) : S.rank≤1 := by
  have hm : S=Matrix.vecMulVec (fun i=>S i 0*S 0 0) (S 0) := by
    funext i j
    change S i j=(S i 0*S 0 0)*S 0 j
    have h := sign_row_products_of_squaredGram_rank_le_one S hS hr i j
    have ht := congrArg (fun x:ℝ=>x*S 0 j) h
    simpa only [mul_assoc,←pow_two,hS,mul_one] using ht
  rw [hm]
  exact Matrix.rank_vecMulVec_le _ _

/-- Literal path squaring followed by thickening: the sign transform is
symmetric, so its matrix square is its row Gram. -/
theorem signGram_square_eq (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,S i j=S j i) : S*S=rowGram S := by
  funext i j
  simp only [Matrix.mul_apply,rowGram]
  apply Finset.sum_congr rfl
  intro k _
  rw [hs k j]


def realSignMatrix {n : Type*} (M : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j=>Real.sign (M i j)

theorem realSignMatrix_sq {n : Type*} (M : Matrix n n ℝ)
    (hn : ∀i j,M i j≠0) : ∀i j,(realSignMatrix M i j)^2=1 := by
  intro i j
  rcases Real.sign_apply_eq_of_ne_zero (M i j) (hn i j) with h|h <;>
    simp [realSignMatrix,h]

/-- Squared magnitude and sign together retain the original signed rank-one
property. This is the algebraic join needed after Corollary 3.2. -/
theorem rank_le_one_of_square_and_sign {n : Type} [Fintype n]
    (M : Matrix n n ℝ) (p : n) (hs : ∀i j,M i j=M j i) (hn : M p p≠0)
    (hmag : (schurSquare M).rank≤1) (hsign : (realSignMatrix M).rank≤1) : M.rank≤1 := by
  have hm (i j : n) : M i j*M p p=M i p*M p j := by
    have hm := minor_eq_zero_of_rank_le_one (schurSquare M) hmag i p j p
    have hsig := minor_eq_zero_of_rank_le_one (realSignMatrix M) hsign i p j p
    have habs : |M i j| * |M p p| =|M i p| * |M p j| := by
      apply (sq_eq_sq₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))).mp
      simpa only [mul_pow,sq_abs,schurSquare] using hm
    change Real.sign (M i j)*Real.sign (M p p)=Real.sign (M i p)*Real.sign (M p j) at hsig
    calc
      M i j*M p p=(|M i j| * |M p p|)*(Real.sign (M i j)*Real.sign (M p p)) := by
        rw [mul_mul_mul_comm,ProductCompatibility.abs_mul_real_sign,
          ProductCompatibility.abs_mul_real_sign]
      _ = (|M i p| * |M p j|)*(Real.sign (M i p)*Real.sign (M p j)) := by rw [habs,hsig]
      _ = M i p*M p j := by
        rw [mul_mul_mul_comm,ProductCompatibility.abs_mul_real_sign,
          ProductCompatibility.abs_mul_real_sign]
  have hout := scalar_outer_of_pivot M p hn hs hm
  have hvec : M=Matrix.vecMulVec (fun i=>(M p p)⁻¹*M i p) (fun j=>M j p) := by
    conv_lhs => rw [hout]
    funext i j
    change (M p p)⁻¹*(M i p*M j p)=((M p p)⁻¹*M i p)*M j p
    ring
  rw [hvec]
  exact Matrix.rank_vecMulVec_le _ _

/-- Every full-support signed symmetric three-state matrix with rank-one
squared magnitudes but higher rank gives an explicit strictly positive,
higher-rank planar target after sign, path-square and Schur-square. -/
theorem signed_magnitude_rank_one_target (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∀i j,M i j=M j i) (hn : ∀i j,M i j≠0)
    (hmag : (schurSquare M).rank≤1) (hr : ¬M.rank≤1) :
    (∀i j,0<schurSquare (realSignMatrix M*realSignMatrix M) i j) ∧
    ¬(schurSquare (realSignMatrix M*realSignMatrix M)).rank≤1 := by
  have hsym : ∀i j,realSignMatrix M i j=realSignMatrix M j i := by
    intro i j
    simp only [realSignMatrix,hs i j]
  rw [signGram_square_eq _ hsym]
  refine ⟨schurSquare_rowGram_positive _ (realSignMatrix_sq M hn),?_⟩
  intro h
  apply hr
  exact rank_le_one_of_square_and_sign M 0 hs (hn 0 0) hmag
    (rank_le_one_of_squaredSignGram_rank_le_one _ (realSignMatrix_sq M hn) h)

end PlanarHom.SignedThreeState
