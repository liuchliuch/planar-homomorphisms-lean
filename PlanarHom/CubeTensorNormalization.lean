import PlanarHom.CubeTensorExponential
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Normalized tensor factors recovered from actual matrix entries

Every normalized two-by-two factor is reconstructed from ratios of entries
of the full tensor matrix. This proves the algebraicity statement without
assuming that exponentials of algebraic logarithmic coefficients are algebraic.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The all-zero Boolean assignment. -/
def zeroColor : ι → Bool := fun _ => false

/-- Vary one coordinate from the all-zero assignment. -/
def oneCoordinate (r : ι) (a : Bool) : ι → Bool := Function.update zeroColor r a

/-- Scalar factors separate from an actual tensor product. -/
theorem tensor_smul (c : ι → ℝ) (F : ι → Matrix Bool Bool ℝ) :
    tensor (fun r => c r • F r) = (∏ r, c r) • tensor F := by
  ext z w
  simp [tensor, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

@[simp] theorem tensor_zeroColor (F : ι → Matrix Bool Bool ℝ) :
    tensor F zeroColor zeroColor = ∏ r, F r false false := rfl

/-- A one-coordinate entry isolates one factor and the other reference diagonals. -/
theorem tensor_oneCoordinate (F : ι → Matrix Bool Bool ℝ) (r : ι) (a b : Bool) :
    tensor F (oneCoordinate r a) (oneCoordinate r b) =
      F r a b * ∏ k ∈ Finset.univ.erase r, F k false false := by
  unfold tensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => F k (oneCoordinate r a k) (oneCoordinate r b k)) (Finset.mem_univ r)]
  simp only [oneCoordinate, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Function.update_of_ne (Finset.mem_erase.mp hk).1, zeroColor]

/-- Normalize each factor's `false,false` entry to one. -/
def normalizedFactor (F : ι → Matrix Bool Bool ℝ) (r : ι) : Matrix Bool Bool ℝ :=
  (F r false false)⁻¹ • F r

@[simp] theorem normalizedFactor_zero_zero (F : ι → Matrix Bool Bool ℝ)
    (hdiag : ∀ r, F r false false ≠ 0) (r : ι) : normalizedFactor F r false false = 1 := by
  simp [normalizedFactor, hdiag r]

/-- Multiplying the normalized tensor by its reference product recovers the tensor. -/
theorem tensor_eq_prod_diagonal_smul_normalized (F : ι → Matrix Bool Bool ℝ)
    (hdiag : ∀ r, F r false false ≠ 0) :
    tensor F = (∏ r, F r false false) • tensor (normalizedFactor F) := by
  unfold normalizedFactor
  rw [tensor_smul, smul_smul, ← Finset.prod_mul_distrib]
  simp [hdiag]

/-- The scalar in the normalized tensor factorization is exactly the full
matrix's all-zero diagonal entry. -/
theorem scalar_tensor_eq_reference_smul_normalized (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hdiag : ∀ r, F r false false ≠ 0) :
    N = N zeroColor zeroColor • tensor (normalizedFactor F) := by
  have hzero : N zeroColor zeroColor = γ * ∏ r, F r false false := by
    rw [hN]
    rfl
  rw [hzero, hN, tensor_eq_prod_diagonal_smul_normalized F hdiag, smul_smul]

/-- Every normalized factor entry is an actual full-matrix entry ratio. -/
theorem normalizedFactor_eq_entry_ratio (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : γ ≠ 0) (hdiag : ∀ r, F r false false ≠ 0) (r : ι) (a b : Bool) :
    normalizedFactor F r a b =
      N (oneCoordinate r a) (oneCoordinate r b) / N zeroColor zeroColor := by
  have hp : (∏ k ∈ Finset.univ.erase r, F k false false) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hdiag k)
  have hprod : (∏ k, F k false false) =
      F r false false * ∏ k ∈ Finset.univ.erase r, F k false false :=
    (Finset.mul_prod_erase Finset.univ (fun k => F k false false) (Finset.mem_univ r)).symm
  rw [hN]
  simp only [normalizedFactor, Matrix.smul_apply, smul_eq_mul, tensor_oneCoordinate,
    tensor_zeroColor, hprod]
  field_simp [hγ, hdiag r, hp]

/-- Algebraicity is inherited from the reconstructed full-matrix ratios. -/
theorem normalizedFactor_isAlgebraic (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (γ : ℝ) (F : ι → Matrix Bool Bool ℝ) (hN : N = γ • tensor F)
    (hγ : γ ≠ 0) (hdiag : ∀ r, F r false false ≠ 0)
    (hAlg : ∀ z w, IsAlgebraic ℚ (N z w)) (r : ι) (a b : Bool) :
    IsAlgebraic ℚ (normalizedFactor F r a b) := by
  rw [normalizedFactor_eq_entry_ratio N γ F hN hγ hdiag]
  rw [div_eq_mul_inv]
  exact (hAlg _ _).mul (hAlg _ _).inv

end PlanarHom.CubeTensorExponential
