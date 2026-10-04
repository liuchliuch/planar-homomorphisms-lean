import PlanarHom.PowerRootCoordinateAnnihilator
import PlanarHom.FixedCharacteristicPolynomialMachines

/-! # Actual FP construction of all coordinate annihilator coefficients

These machines produce monic rational polynomials annihilating the desired
coordinates. They do not select or compute roots of those polynomials.
-/

noncomputable section
namespace PlanarHom.PowerRootCoordinateMachines
open Complexity FixedFieldArithmetic RationalCircuits BinaryArithmetic
open ArithmeticCircuitPrimitives PairProjectionMachines
open PowerRootCoordinateAnnihilator

theorem fp_tensor_entry {α J : Type} [Fintype J] [DecidableEq J]
    (ea : BitEncoding α) (A : α → Matrix J J ℚ)
    (hA : ∀ i j, FP ea BitEncoding.rat (fun a => A a i j)) (n : ℕ)
    (i j : TensorSumEigenvalues.Index J n) :
    FP ea BitEncoding.rat (fun a => TensorSumEigenvalues.matrix n (A a) i j) := by
  induction n with
  | zero => exact fp_const ea BitEncoding.rat 0
  | succ n ih =>
    have hl := ((hA i.1 j.1).pair
      (fp_const ea BitEncoding.rat ((1 : Matrix (TensorSumEigenvalues.Index J n)
        (TensorSumEigenvalues.Index J n) ℚ) i.2 j.2))).comp fp_rational_multiplication
    have hr := ((fp_const ea BitEncoding.rat ((1 : Matrix J J ℚ) i.1 j.1)).pair
      (ih i.2 j.2)).comp fp_rational_multiplication
    exact (hl.pair hr).comp fp_rational_addition

variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)

theorem fp_rootMatrix_entry (n : ℕ) (c : K) (i j : Fin n × Fin d) :
    FP (numberFieldEncoding basis) BitEncoding.rat
      (fun y => rootMatrix basis n c y i j) := by
  have hm := ((fp_const (numberFieldEncoding basis) (numberFieldEncoding basis) (c^n)).pair
    (fp_id (numberFieldEncoding basis))).comp (fp_multiplication basis)
  unfold rootMatrix PowerRootLiftMatrix.lift
  split_ifs
  · exact fp_const _ _ 1
  · exact fp_const _ _ 0
  · exact fp_const _ _ 0
  · exact hm.comp (fp_multiplication_matrix basis j.2 i.2)
  · exact fp_const _ _ 0

theorem fp_tracePolynomial_coeff (n : ℕ) (c : K) (k : ℕ) :
    FP (numberFieldEncoding basis) BitEncoding.rat
      (fun y => (tracePolynomial basis n c y).coeff k) := by
  apply FixedCharacteristicPolynomialMachines.fp_charpoly_coeff
  intro i j
  exact fp_tensor_entry _ (rootMatrix basis n c) (fp_rootMatrix_entry basis n c) _ i j

theorem fp_coordinatePolynomial_coeff (n : ℕ) (i : Fin d) (k : ℕ) :
    FP (numberFieldEncoding basis) BitEncoding.rat
      (fun y => (coordinatePolynomial basis n i y).coeff k) :=
  fp_tracePolynomial_coeff basis n (dual basis i) k

/-- Any fixed coefficient prefix is materialized in the existing framed vector
codec. Taking `L` one greater than the fixed matrix dimension includes all
coefficients, including the leading one. -/
theorem fp_coordinateCoefficients (n : ℕ) (i : Fin d) (L : ℕ) :
    FP (numberFieldEncoding basis) (BitEncoding.rat.vector L)
      (fun y k => (coordinatePolynomial basis n i y).coeff k.val) :=
  FixedVectorMachines.fp_assemble _ _ _ _ (fun k => fp_coordinatePolynomial_coeff basis n i k.val)

def coefficients (n : ℕ) (i : Fin d) (y : K) : Fin ((n*d)^d+1) → ℚ :=
  fun k => (coordinatePolynomial basis n i y).coeff k.val

theorem fp_coefficients (n : ℕ) (i : Fin d) :
    FP (numberFieldEncoding basis) (BitEncoding.rat.vector ((n*d)^d+1))
      (coefficients basis n i) := fp_coordinateCoefficients basis n i _

theorem coefficients_leading_one (n : ℕ) (i : Fin d) (y : K) :
    coefficients basis n i y (Fin.last ((n*d)^d)) = 1 := by
  unfold coefficients
  simpa [coordinatePolynomial_natDegree_eq basis n i y] using
    (coordinatePolynomial_monic basis n i y).coeff_natDegree

theorem coefficients_root (n : ℕ) (hn : 0 < n) (i : Fin d) (x : K) :
    ∑ k : Fin ((n*d)^d+1), coefficients basis n i (x^n) k *
      basis.equivFun x i ^ k.val = 0 := by
  have h := coordinatePolynomial_root basis n hn i x
  rw [Polynomial.eval_eq_sum_range, coordinatePolynomial_natDegree_eq basis n i (x^n)] at h
  change (∑ k : Fin ((n*d)^d+1), (coordinatePolynomial basis n i (x^n)).coeff k.val *
      basis.equivFun x i ^ k.val) = 0
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (coordinatePolynomial basis n i (x^n)).coeff k * basis.equivFun x i ^ k)
    ((n*d)^d+1)]
  exact h

end PlanarHom.PowerRootCoordinateMachines
