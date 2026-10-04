import PlanarHom.FiniteRationalCircuits
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

/-! # Actual rational circuits for fixed characteristic-polynomial coefficients -/

noncomputable section
namespace PlanarHom.FixedCharacteristicPolynomialMachines
open Complexity RationalCircuits BinaryArithmetic ArithmeticCircuitPrimitives

theorem fp_fixedMvPolynomial {α I : Type} (ea : BitEncoding α)
    (p : MvPolynomial I ℚ) (f : α → I → ℚ)
    (hf : ∀ i, FP ea BitEncoding.rat (fun a => f a i)) :
    FP ea BitEncoding.rat (fun a => MvPolynomial.eval (f a) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using fp_const ea BitEncoding.rat c
  | add p q hp hq =>
    exact ((hp.pair hq).comp fp_rational_addition).congr (fun a => by simp)
  | mul_X p i hp =>
    exact ((hp.pair (hf i)).comp fp_rational_multiplication).congr (fun a => by simp)

/-- Every characteristic coefficient is the evaluation of its fixed universal
multivariate polynomial at the input matrix entries. -/
theorem fp_charpoly_coeff {α I : Type} [Fintype I] [DecidableEq I]
    (ea : BitEncoding α) (M : α → Matrix I I ℚ)
    (hM : ∀ i j, FP ea BitEncoding.rat (fun a => M a i j)) (k : ℕ) :
    FP ea BitEncoding.rat (fun a => (M a).charpoly.coeff k) := by
  have h := fp_fixedMvPolynomial ea ((Matrix.charpoly.univ ℚ I).coeff k)
    (fun a ij => M a ij.1 ij.2) (fun ij => hM ij.1 ij.2)
  exact h.congr (fun a => Matrix.charpoly.univ_coeff_eval₂Hom I (RingHom.id ℚ)
    (fun ij => M a ij.1 ij.2) k)

end PlanarHom.FixedCharacteristicPolynomialMachines
