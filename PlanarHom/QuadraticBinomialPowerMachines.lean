import PlanarHom.MaterializedPowerMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.ListReverseMachines
import PlanarHom.BinaryDivisionMachine
import PlanarHom.NatListSumMachines
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.QuadraticAlgebra

/-! Actual binomial coefficients and quadratic branch powers in a fixed field.
Every variable exponent and factorial is paid for by a literal unary cap. -/
namespace PlanarHom.QuadraticBinomialPowerMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

omit [Algebra ℚ K] in
private theorem factorial_range (n : ℕ) :
    ((List.range n).map (fun j => ((j + 1 : ℕ) : K))).prod = (n.factorial : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih, Nat.factorial_succ, Nat.cast_mul]
    exact mul_comm _ _

/-- Factorials are computed by materializing the range and multiplying its casts. -/
theorem fp_factorial : FP BitEncoding.unaryNat (numberFieldEncoding basis)
    (fun n : ℕ => (n.factorial : K)) := by
  have hm := ListMapMachines.fp_map BitEncoding.nat (numberFieldEncoding basis)
    (fun j : ℕ => ((j + 1 : ℕ) : K))
    (BinaryArithmetic.fp_successor.comp (FixedFieldPolynomialMachines.fp_natCast basis))
  exact ((UnaryRangeMachines.fp_range.comp hm).comp
    (MaterializedFieldListMachines.fp_product basis)).congr (fun n => by
      simpa only [Function.comp_apply, List.map_reverse, List.prod_reverse] using factorial_range (K := K) n)

private theorem choose_field_formula (n j : ℕ) (h : j ≤ n) :
    (n.choose j : K) = (n.factorial : K) /
      ((j.factorial : K) * ((n - j).factorial : K)) := by
  letI : CharZero K := ((algebraMap ℚ K).charZero_iff (algebraMap ℚ K).injective).mp inferInstance
  have hj : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnj : ((n-j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-j)
  apply (eq_div_iff (mul_ne_zero hj hnj)).2
  have hnat := Nat.choose_mul_factorial_mul_factorial h
  simpa only [Nat.cast_mul, mul_assoc] using congrArg (fun m : ℕ => (m : K)) hnat

/-- The lower argument is binary; factorial calls are capped by the unary upper
argument. The output is the ordinary binomial coefficient, including zero past n. -/
theorem fp_choose : FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    (numberFieldEncoding basis) (fun p : ℕ × ℕ => (p.1.choose p.2 : K)) := by
  let input := BitEncoding.unaryNat.prod BitEncoding.nat
  have hn := fp_fst BitEncoding.unaryNat BitEncoding.nat
  have hj := fp_snd BitEncoding.unaryNat BitEncoding.nat
  have hnb := hn.comp UnaryNatConversionMachine.fp_conversion
  have hju := (hn.pair hj).comp (show FP _ _ (fun p : ℕ × ℕ => min p.1 p.2) from
    ⟨BoundedUnaryMachines.computer⟩)
  have hdiff := (hnb.pair hj).comp BinaryArithmetic.fp_subtraction
  have hdu := (hn.pair hdiff).comp (show FP _ _ (fun p : ℕ × ℕ => min p.1 p.2) from
    ⟨BoundedUnaryMachines.computer⟩)
  have hden := ((hju.comp (fp_factorial basis)).pair (hdu.comp (fp_factorial basis))).comp
    (FixedFieldArithmetic.fp_multiplication basis)
  have hquot := ((hn.comp (fp_factorial basis)).pair hden).comp
    (FixedFieldArithmetic.fp_division basis)
  have htest := (hnb.pair hj).comp BinaryArithmetic.fp_comparison
  exact (htest.ite (fp_const input (numberFieldEncoding basis) 0) hquot).congr (fun p => by
    dsimp only [Function.comp_apply, id_eq]
    by_cases h : p.2 ≤ p.1
    · simp only [show ¬p.1 < p.2 by omega, ↓reduceIte, min_eq_right h,
        min_eq_right (Nat.sub_le p.1 p.2)]
      exact (choose_field_formula (K := K) p.1 p.2 h).symm
    · simp [show p.1 < p.2 by omega, Nat.choose_eq_zero_of_lt (show p.1 < p.2 by omega)])

/-- n is unary, while c and D are arbitrary materialized elements of the fixed field. -/
noncomputable def inputEncoding : BitEncoding (ℕ × (K × K)) :=
  BitEncoding.unaryNat.prod ((numberFieldEncoding basis).prod (numberFieldEncoding basis))

def term (p : ℕ × (K × K)) (j : ℕ) : K :=
  (p.1.choose j : K) * p.2.1 ^ (p.1-j) * p.2.2 ^ (j/2)

theorem fp_term : FP ((inputEncoding basis).prod BitEncoding.nat)
    (numberFieldEncoding basis) (fun p : (ℕ × (K × K)) × ℕ => term p.1 p.2) := by
  let e := numberFieldEncoding basis
  have hp := fp_fst (inputEncoding basis) BitEncoding.nat
  have hj := fp_snd (inputEncoding basis) BitEncoding.nat
  have hn := hp.comp (fp_fst BitEncoding.unaryNat (e.prod e))
  have hcd := hp.comp (fp_snd BitEncoding.unaryNat (e.prod e))
  have hc := hcd.comp (fp_fst e e)
  have hd := hcd.comp (fp_snd e e)
  have hnb := hn.comp UnaryNatConversionMachine.fp_conversion
  have hchoose := (hn.pair hj).comp (fp_choose basis)
  have hdiff := (hnb.pair hj).comp BinaryArithmetic.fp_subtraction
  have hhalf := ((hj.pair (fp_const ((inputEncoding basis).prod BitEncoding.nat)
    BitEncoding.nat 2)).comp BinaryArithmetic.fp_division).comp
      (fp_fst BitEncoding.nat BitEncoding.nat)
  have hcpow := (hn.pair (hc.pair hdiff)).comp (MaterializedPowerMachines.fp_boundedPower basis)
  have hdpow := (hn.pair (hd.pair hhalf)).comp (MaterializedPowerMachines.fp_boundedPower basis)
  exact ((((hchoose.pair hcpow).comp (FixedFieldArithmetic.fp_multiplication basis)).pair hdpow).comp
    (FixedFieldArithmetic.fp_multiplication basis)).congr (fun p => by
      dsimp only [term, Function.comp_apply, id_eq]
      by_cases h : p.2 ≤ p.1.1
      · rw [min_eq_right (Nat.sub_le _ _), min_eq_right ((Nat.div_le_self _ _).trans h)]
      · simp [Nat.choose_eq_zero_of_lt (show p.1.1 < p.2 by omega)])

def component (parity : ℕ) (p : ℕ × (K × K)) : K :=
  ((List.range (p.1+1)).map (fun j => if j % 2 = parity then term p j else 0)).sum

def branchPower (p : ℕ × (K × K)) : K × K := (component 0 p, component 1 p)

theorem fp_component (parity : ℕ) : FP (inputEncoding basis) (numberFieldEncoding basis)
    (component parity) := by
  have hj := fp_snd (inputEncoding basis) BitEncoding.nat
  have hmod := ((hj.pair (fp_const ((inputEncoding basis).prod BitEncoding.nat)
    BitEncoding.nat 2)).comp BinaryArithmetic.fp_division).comp
      (fp_snd BitEncoding.nat BitEncoding.nat)
  have htest := (hmod.pair (fp_const ((inputEncoding basis).prod BitEncoding.nat)
    BitEncoding.nat parity)).comp NatListSumMachines.fp_equal
  have hbody := htest.ite (fp_term basis)
    (fp_const ((inputEncoding basis).prod BitEncoding.nat) (numberFieldEncoding basis) 0)
  have hn := fp_fst BitEncoding.unaryNat ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hsucc := (UnaryPolynomialMachines.fp_offset 1).congr (fun n => Nat.add_comm 1 n)
  have hrange := ((hn.comp hsucc).comp UnaryRangeMachines.fp_range).comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)
  have hmap := ((fp_id (inputEncoding basis)).pair hrange).comp
    (ListContextMachines.fp_mapWithContext (inputEncoding basis) BitEncoding.nat
      (numberFieldEncoding basis) _ hbody)
  exact (hmap.comp (MaterializedFieldListMachines.fp_sum basis)).congr
    (fun p => by simp only [Function.comp_apply, id_eq, component, List.reverse_reverse])

/-- An actual polynomial-time pair of even/odd coefficient sums, with varying
field inputs and no dynamic iteration-size assumption. -/
theorem fp_branchPower : FP (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) branchPower :=
  (fp_component basis 0).pair (fp_component basis 1)

omit [Algebra ℚ K] in
theorem component_eq_sum (parity : ℕ) (p : ℕ × (K × K)) :
    component parity p = ∑ j ∈ Finset.range (p.1+1),
      if j % 2 = parity then (p.1.choose j : K) * p.2.1 ^ (p.1-j) * p.2.2 ^ (j/2) else 0 := by
  simpa only [component, term, List.toFinset_range] using
    (List.sum_toFinset (fun j => if j % 2 = parity then term p j else 0)
      (List.nodup_range)).symm

omit [Algebra ℚ K] in
private theorem generator_power (D : K) (n : ℕ) :
    (⟨0,1⟩ : QuadraticAlgebra K D 0)^n =
      ⟨if n % 2 = 0 then D^(n/2) else 0,
        if n % 2 = 1 then D^(n/2) else 0⟩ := by
  have hs : (⟨0,1⟩ : QuadraticAlgebra K D 0)^2 = (D : QuadraticAlgebra K D 0) := by
    ext <;> simp [pow_two]
  have hn : n = 2*(n/2)+n%2 := by omega
  conv_lhs => rw [hn, pow_add, pow_mul, hs, ← QuadraticAlgebra.coe_pow]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · ext <;> simp [-QuadraticAlgebra.coe_pow, h]
  · ext <;> simp [-QuadraticAlgebra.coe_pow, h]

omit [Algebra ℚ K] in
private theorem quadratic_power_expansion (c D : K) (n : ℕ) :
    (⟨c,1⟩ : QuadraticAlgebra K D 0)^n =
      ∑ j ∈ Finset.range (n+1),
        (⟨0,1⟩ : QuadraticAlgebra K D 0)^j *
          (c : QuadraticAlgebra K D 0)^(n-j) * (n.choose j : QuadraticAlgebra K D 0) := by
  have h : (⟨c,1⟩ : QuadraticAlgebra K D 0) =
      (⟨0,1⟩ : QuadraticAlgebra K D 0) + (c : QuadraticAlgebra K D 0) := by
    ext <;> simp
  rw [h, add_pow]

omit [Algebra ℚ K] in
/-- Exact coefficient semantics in the formal quadratic algebra, without choosing
a root of D or requiring D to be nonsquare. -/
theorem branchPower_eq_quadraticPower (n : ℕ) (c D : K) :
    branchPower (n,(c,D)) =
      (((⟨c,1⟩ : QuadraticAlgebra K D 0)^n).re,
        ((⟨c,1⟩ : QuadraticAlgebra K D 0)^n).im) := by
  apply Prod.ext
  · change component 0 (n,(c,D)) = _
    rw [component_eq_sum, quadratic_power_expansion]
    change _ = (QuadraticAlgebra.reₗ D 0) _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [generator_power, ← QuadraticAlgebra.coe_pow]
    by_cases h : j%2=0 <;>
      simp [QuadraticAlgebra.reₗ, -QuadraticAlgebra.coe_pow, h, mul_comm, mul_left_comm, mul_assoc]
  · change component 1 (n,(c,D)) = _
    rw [component_eq_sum, quadratic_power_expansion]
    change _ = (QuadraticAlgebra.imₗ D 0) _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [generator_power, ← QuadraticAlgebra.coe_pow]
    by_cases h : j%2=1 <;>
      simp [QuadraticAlgebra.imₗ, -QuadraticAlgebra.coe_pow, h, mul_comm, mul_left_comm, mul_assoc]

/-- The semantic quadratic-power coefficient function inherits the actual machine. -/
theorem fp_quadraticPower_coefficients : FP (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (fun p : ℕ × (K × K) =>
      (((⟨p.2.1,1⟩ : QuadraticAlgebra K p.2.2 0)^p.1).re,
        ((⟨p.2.1,1⟩ : QuadraticAlgebra K p.2.2 0)^p.1).im)) :=
  (fp_branchPower basis).congr (fun p => branchPower_eq_quadraticPower p.1 p.2.1 p.2.2)

end PlanarHom.QuadraticBinomialPowerMachines
