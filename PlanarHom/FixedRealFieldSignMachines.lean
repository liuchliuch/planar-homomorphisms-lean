import PlanarHom.FixedRealFieldSignBounds
import PlanarHom.RationalOrderMachines
import PlanarHom.BinaryMultiplicationMachine
import PlanarHom.ConditionalMachines

/-! Actual finite arithmetic circuits for the sign-separation construction. -/
noncomputable section
namespace PlanarHom.FixedRealFieldSign
open Complexity ArithmeticCircuitPrimitives RationalCircuits PairProjectionMachines BinaryArithmetic
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)

theorem fp_nat_sum {α ι : Type} (ea : BitEncoding α) (s : Finset ι) (f : α → ι → ℕ)
    (hf : ∀ i, FP ea BitEncoding.nat (fun a => f a i)) :
    FP ea BitEncoding.nat (fun a => ∑ i ∈ s, f a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.nat 0
  | @insert i s hi ih =>
    exact (((hf i).pair ih).comp BinaryArithmetic.fp_addition).congr
      (fun a => by simp [Finset.sum_insert, hi])

theorem fp_coordinateMass : FP (numberFieldEncoding basis) BitEncoding.nat (coordinateMass basis) := by
  exact fp_nat_sum _ Finset.univ _ (fun i =>
    ((FixedFieldArithmetic.fp_coordinate basis i).comp fp_rat_num).comp fp_int_natAbs)

theorem fp_inverseBound (M : ℕ) :
    FP (numberFieldEncoding basis) BitEncoding.nat (inverseBound basis M) := by
  have hi := (FixedFieldArithmetic.fp_inverse basis).comp (fp_coordinateMass basis)
  have hm := ((fp_const (numberFieldEncoding basis) BitEncoding.nat M).pair hi).comp
    BinaryArithmetic.fp_multiplication
  exact ((fp_const (numberFieldEncoding basis) BitEncoding.nat 1).pair hm).comp
    BinaryArithmetic.fp_addition

theorem fp_precision (M : ℕ) :
    FP (numberFieldEncoding basis) BitEncoding.nat (precision basis M) := by
  have hh := ((fp_const (numberFieldEncoding basis) BitEncoding.nat 4).pair
    (fp_inverseBound basis M)).comp BinaryArithmetic.fp_multiplication
  have hc := ((fp_const (numberFieldEncoding basis) BitEncoding.nat 1).pair
    (fp_coordinateMass basis)).comp BinaryArithmetic.fp_addition
  exact (hh.pair hc).comp BinaryArithmetic.fp_multiplication

theorem fp_approximation (f : Fin d → ℕ → ℚ)
    (hf : ∀ i, FP BitEncoding.nat BitEncoding.rat (f i)) (M : ℕ) :
    FP (numberFieldEncoding basis) BitEncoding.rat (approximation basis f M) := by
  exact FiniteRationalCircuits.fp_sum _ Finset.univ _ (fun i =>
    ((FixedFieldArithmetic.fp_coordinate basis i).pair
      ((fp_precision basis M).comp (hf i))).comp fp_rational_multiplication)

theorem fp_positive_of_approximations (embedding : K →+* ℝ) (f : Fin d → ℕ → ℚ)
    (hfp : ∀ i, FP BitEncoding.nat BitEncoding.rat (f i))
    (hf : ∀ i N, |(f i N : ℝ) - embedding (basis i)| ≤ 1 / ((N : ℝ) + 1)) :
    FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x)) := by
  classical
  obtain ⟨M, _, hM⟩ := exists_basis_bound basis embedding
  exact ((fp_approximation basis f hfp M).comp RationalOrderMachines.fp_positive).congr
    (fun x => by
      change decide (0 < approximation basis f M x) = decide (0 < embedding x)
      simp only [decide_eq_decide]
      exact approximation_positive_iff basis embedding f hf M hM x)

/-- A negative test reuses the same positive test after exact field negation. -/
theorem fp_negative_of_positive (embedding : K →+* ℝ)
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x))) :
    FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (embedding x < 0)) := by
  exact ((FixedFieldArithmetic.fp_negation basis).comp hpos).congr
    (fun x => by simp)

theorem fp_nonnegative_of_positive (embedding : K →+* ℝ)
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x))) :
    FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 ≤ embedding x)) := by
  exact ((fp_negative_of_positive basis embedding hpos).comp
    (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun x => by
      by_cases hx : embedding x < 0
      · simp [hx, not_le.mpr hx]
      · simp [hx, not_lt.mp hx])

/-- Comparison subtracts the two materialized exact field inputs. -/
theorem fp_less_of_positive (embedding : K →+* ℝ)
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x))) :
    FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
      (fun p : K × K => decide (embedding p.1 < embedding p.2)) := by
  have hs := (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)).pair
    (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  exact ((hs.comp (FixedFieldArithmetic.fp_subtraction basis)).comp hpos).congr
    (fun p => by simp)

def sign (embedding : K →+* ℝ) (x : K) : ℤ :=
  if 0 < embedding x then 1 else if embedding x < 0 then -1 else 0

/-- The three-valued sign is emitted in the canonical integer encoding. -/
theorem fp_sign_of_positive (embedding : K →+* ℝ)
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x))) :
    FP (numberFieldEncoding basis) BitEncoding.int (sign embedding) := by
  have hneg := fp_negative_of_positive basis embedding hpos
  exact hpos.ite (fp_const _ _ 1)
    (hneg.ite (fp_const _ _ (-1)) (fp_const _ _ 0))

end PlanarHom.FixedRealFieldSign
