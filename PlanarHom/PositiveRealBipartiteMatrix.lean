import PlanarHom.PositiveRealCoreGrams
import PlanarHom.PositiveUnitDiagonalRigidity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! NEW literal decorated bipartite Gram identities and row facts. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveRealCore
variable {I : Type} [Fintype I] [DecidableEq I]

def doubleMatrix (B : Matrix I I ℝ) : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  Matrix.fromBlocks 0 B B.transpose 0

def leftGram (B : Matrix I I ℝ) (μ ν : I → ℝ) : Matrix I I ℝ :=
  decorated B μ ν * (decorated B μ ν).transpose

def rightGram (B : Matrix I I ℝ) (μ ν : I → ℝ) : Matrix I I ℝ :=
  (decorated B μ ν).transpose * decorated B μ ν

theorem doubleMatrix_transpose (B : Matrix I I ℝ) : (doubleMatrix B).transpose=doubleMatrix B := by
  ext i j
  cases i <;> cases j <;> rfl

theorem decorated_doubleMatrix (B : Matrix I I ℝ) (μ ν : I → ℝ) :
    decorated (doubleMatrix B) (Sum.elim μ ν) (Sum.elim μ ν)=doubleMatrix (decorated B μ ν) := by
  ext i j
  cases i <;> cases j <;> simp [decorated_entry,doubleMatrix,Matrix.transpose_apply] <;> ring

theorem doubleMatrix_square (B : Matrix I I ℝ) :
    doubleMatrix B * doubleMatrix B = Matrix.fromBlocks (B*B.transpose) 0 0 (B.transpose*B) := by
  simp [doubleMatrix,Matrix.fromBlocks_multiply]

theorem unit_rows_nonzero (B : Matrix I I ℝ) (hB : IsUnit B) : ∀i,B i≠0 := by
  intro i hz
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)) i) i
  simp [Matrix.mul_apply,hz] at h

theorem unit_rows_nonproportional (B : Matrix I I ℝ) (hB : IsUnit B)
    {i j : I} (hij : i≠j) (t : ℝ) : B i≠t • B j := by
  intro he
  have hprod : (B*B⁻¹) i i=t*(B*B⁻¹) j i := by
    simp only [Matrix.mul_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h := congrFun he k
    simp only [Pi.smul_apply,smul_eq_mul] at h
    rw [h]
    ring
  rw [Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)] at hprod
  simp [Matrix.one_apply,hij,hij.symm] at hprod

theorem doubleMatrix_rows_nonzero (B : Matrix I I ℝ) (hB : IsUnit B) :
    ∀i,doubleMatrix B i≠0 := by
  intro i hz
  cases i with
  | inl i =>
    apply unit_rows_nonzero B hB i
    funext j
    exact congrFun hz (.inr j)
  | inr i =>
    apply unit_rows_nonzero B.transpose ((Matrix.isUnit_transpose B).mpr hB) i
    funext j
    exact congrFun hz (.inl j)

theorem doubleMatrix_rows_nonproportional (B : Matrix I I ℝ) (hB : IsUnit B)
    {i j : I⊕I} (hij : i≠j) (t : ℝ) : doubleMatrix B i≠t • doubleMatrix B j := by
  intro he
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      apply unit_rows_nonproportional B hB (fun h=>hij (congrArg Sum.inl h)) t
      funext k
      exact congrFun he (.inr k)
    | inr j =>
      apply unit_rows_nonzero B hB i
      funext k
      have h := congrFun he (.inr k)
      simpa [doubleMatrix] using h
  | inr i =>
    cases j with
    | inl j =>
      apply unit_rows_nonzero B.transpose ((Matrix.isUnit_transpose B).mpr hB) i
      funext k
      have h := congrFun he (.inl k)
      simpa [doubleMatrix] using h
    | inr j =>
      apply unit_rows_nonproportional B.transpose ((Matrix.isUnit_transpose B).mpr hB)
        (fun h=>hij (congrArg Sum.inr h)) t
      funext k
      exact congrFun he (.inl k)

theorem decorated_isUnit (B : Matrix I I ℝ) (hB : IsUnit B)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) : IsUnit (decorated B μ ν) := by
  have hleft : (rootDiagonal μ).PosDef := Matrix.posDef_diagonal_iff.mpr (fun i=>Real.sqrt_pos.mpr (hμ i))
  have hright : (rootDiagonal ν).PosDef := Matrix.posDef_diagonal_iff.mpr (fun i=>Real.sqrt_pos.mpr (hν i))
  exact (hleft.isUnit.mul hB).mul hright.isUnit

theorem leftGram_posDef (B : Matrix I I ℝ) (hB : IsUnit B)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) : (leftGram B μ ν).PosDef := by
  have h := Matrix.PosDef.mul_conjTranspose_self (decorated B μ ν)
    (Matrix.vecMul_injective_iff_isUnit.mpr (decorated_isUnit B hB μ ν hμ hν))
  have ht : (decorated B μ ν).conjTranspose=(decorated B μ ν).transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  simpa only [ht] using h

theorem rightGram_posDef (B : Matrix I I ℝ) (hB : IsUnit B)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i) : (rightGram B μ ν).PosDef := by
  have h := Matrix.PosDef.conjTranspose_mul_self (decorated B μ ν)
    (Matrix.mulVec_injective_iff_isUnit.mpr (decorated_isUnit B hB μ ν hμ hν))
  have ht : (decorated B μ ν).conjTranspose=(decorated B μ ν).transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  simpa only [ht] using h

theorem leftGram_diagonal (B : Matrix I I ℝ) (μ ν : I → ℝ)
    (hμ : ∀i,0≤μ i) (hν : ∀i,0≤ν i) (i : I) :
    leftGram B μ ν i i = μ i * ∑j,B i j^2*ν j := by
  simp only [leftGram,Matrix.mul_apply,Matrix.transpose_apply,decorated_entry,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ha := Real.sq_sqrt (hμ i)
  have hb := Real.sq_sqrt (hν j)
  calc
    _ = (Real.sqrt (μ i))^2 * (B i j)^2 * (Real.sqrt (ν j))^2 := by ring
    _ = _ := by rw [ha,hb]; ring

theorem rightGram_diagonal (B : Matrix I I ℝ) (μ ν : I → ℝ)
    (hμ : ∀i,0≤μ i) (hν : ∀i,0≤ν i) (j : I) :
    rightGram B μ ν j j = ν j * ∑i,B i j^2*μ i := by
  simp only [rightGram,Matrix.mul_apply,Matrix.transpose_apply,decorated_entry,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have ha := Real.sq_sqrt (hμ i)
  have hb := Real.sq_sqrt (hν j)
  calc
    _ = (Real.sqrt (μ i))^2 * (B i j)^2 * (Real.sqrt (ν j))^2 := by ring
    _ = _ := by rw [ha,hb]; ring

end PlanarHom.PositiveRealCore
