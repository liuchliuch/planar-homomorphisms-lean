import PlanarHom.FixedFieldArithmeticMachines
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Actual bit-level transport between fixed rational field representations

Every fixed rational-linear map is compiled from finite rational circuits and
exact coordinate assembly. This covers basis changes, field inclusions, and
fixed linear descent maps on values known to lie in an embedded base field.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedFieldEncodingTransport
open Complexity FixedFieldArithmetic FiniteRationalCircuits RationalCircuits
variable {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
variable {d e : ℕ} (bK : Module.Basis (Fin d) ℚ K) (bL : Module.Basis (Fin e) ℚ L)

/-- The finite rational matrix of the actual linear map computes its coordinates. -/
theorem coordinate_linearMap (f : K →ₗ[ℚ] L) (x : K) (i : Fin e) :
    bL.equivFun (f x) i = ∑ j, bL.equivFun (f (bK j)) i * bK.equivFun x j := by
  conv_lhs => rw [← bK.sum_equivFun x]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- This is a genuine polynomial-time machine, not a free change of output type. -/
theorem fp_linearMap (f : K →ₗ[ℚ] L) :
    FP (numberFieldEncoding bK) (numberFieldEncoding bL) f := by
  apply fp_of_coordinates bL (numberFieldEncoding bK)
  intro i
  have h := FiniteRationalCircuits.fp_sum (numberFieldEncoding bK) Finset.univ
    (fun x j => bL.equivFun (f (bK j)) i * bK.equivFun x j)
    (fun j => ((fp_const (numberFieldEncoding bK) BitEncoding.rat (bL.equivFun (f (bK j)) i)).pair
      (fp_coordinate bK j)).comp BinaryArithmetic.fp_rational_multiplication)
  exact h.congr (fun x => (coordinate_linearMap bK bL f x i).symm)

/-- Fixed field inclusions are compiled by their actual rational coordinate map. -/
theorem fp_fieldEmbedding (f : K →ₐ[ℚ] L) :
    FP (numberFieldEncoding bK) (numberFieldEncoding bL) f := fp_linearMap bK bL f.toLinearMap

/-- Changing fixed rational bases is an actual bit algorithm in both directions. -/
theorem fp_changeBasis {d' : ℕ} (bK' : Module.Basis (Fin d') ℚ K) :
    FP (numberFieldEncoding bK) (numberFieldEncoding bK') id :=
  fp_linearMap bK bK' (LinearMap.id : K →ₗ[ℚ] K)

/-- A fixed embedding admits a compiled linear retraction, correct on its image.
No claim is made that this retraction is a field homomorphism away from that image. -/
theorem exists_fp_leftInverse (f : K →ₗ[ℚ] L) (hf : Function.Injective f) :
    ∃ g : L →ₗ[ℚ] K, Function.LeftInverse g f ∧
      FP (numberFieldEncoding bL) (numberFieldEncoding bK) g := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  exact ⟨g, fun x => DFunLike.congr_fun hg x, fp_linearMap bL bK g⟩

end PlanarHom.FixedFieldEncodingTransport
