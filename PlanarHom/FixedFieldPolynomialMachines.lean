import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.UnaryNatConversionMachine
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Actual fixed-field finite circuits and fixed-polynomial family evaluation. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedFieldPolynomialMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- A fixed finite sum compiles each summand and performs genuine field additions. -/
theorem fp_sum {α I : Type} (ea : BitEncoding α) (S : Finset I) (f : α → I → K)
    (hf : ∀ i ∈ S, FP ea (numberFieldEncoding basis) (fun a => f a i)) :
    FP ea (numberFieldEncoding basis) (fun a => ∑ i ∈ S, f a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using fp_const ea (numberFieldEncoding basis) (0 : K)
  | @insert i S hi ih =>
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact (((hf i (Finset.mem_insert_self _ _)).pair ht).comp
      (FixedFieldArithmetic.fp_addition basis)).congr (fun a => by simp [hi])

/-- A fixed natural exponent is a finite multiplication circuit. -/
theorem fp_fixedPower (k : ℕ) : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun x : K => x ^ k) := by
  induction k with
  | zero => simpa using fp_const (numberFieldEncoding basis) (numberFieldEncoding basis) (1 : K)
  | succ k ih =>
    exact ((ih.pair (fp_id (numberFieldEncoding basis))).comp
      (FixedFieldArithmetic.fp_multiplication basis)).congr (fun x => (pow_succ x k).symm)

/-- Rational inclusion is compiled from its literal fixed-basis coordinate map. -/
theorem fp_ratCast : FP BitEncoding.rat (numberFieldEncoding basis) (algebraMap ℚ K) := by
  apply FixedFieldArithmetic.fp_of_coordinates
  intro i
  exact (((fp_id BitEncoding.rat).pair
    (fp_const BitEncoding.rat BitEncoding.rat (basis.equivFun (1 : K) i))).comp
    BinaryArithmetic.fp_rational_multiplication).congr (fun x => by
      have h := congrArg (fun v : Fin dimension → ℚ => v i) (basis.equivFun.map_smul x (1 : K))
      simpa only [Algebra.smul_def, mul_one, Pi.smul_apply, smul_eq_mul] using h.symm)

theorem fp_natCast : FP BitEncoding.nat (numberFieldEncoding basis) (fun n : ℕ => (n : K)) := by
  exact ((fp_nat_int.comp fp_int_rat).comp (fp_ratCast basis)).congr (fun n => by simp)

/-- Polynomial coefficients and degree are fixed source data, not runtime advice. -/
theorem fp_eval (p : Polynomial K) : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun x => p.eval x) := by
  have h := fp_sum basis (numberFieldEncoding basis) p.support
    (fun x i => p.coeff i * x ^ i) (by
      intro i _
      exact (((fp_const (numberFieldEncoding basis) (numberFieldEncoding basis) (p.coeff i)).pair
        (fp_fixedPower basis i)).comp (FixedFieldArithmetic.fp_multiplication basis)))
  exact h.congr (fun x => (Polynomial.eval_eq_sum (p := p) (x := x)).symm)

/-- Source3.10(P)'s integer family is computable in polynomial bit time. -/
theorem fp_unaryPolynomial (p : Polynomial K) : FP BitEncoding.unaryNat
    (numberFieldEncoding basis) (fun n : ℕ => p.eval (n : K)) :=
  (UnaryNatConversionMachine.fp_conversion.comp (fp_natCast basis)).comp (fp_eval basis p)

/-- All entries of a fixed polynomial alphabet are evaluated with the existing
fixed-width vector codec, retaining the unary source parameter convention. -/
theorem fp_polynomialFamily {t : ℕ} (F : Fin t → Polynomial K) :
    FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t)
      (fun n i => (F i).eval (n : K)) :=
  FixedVectorMachines.fp_assemble _ _ _ _ (fun i => fp_unaryPolynomial basis (F i))

end PlanarHom.FixedFieldPolynomialMachines
