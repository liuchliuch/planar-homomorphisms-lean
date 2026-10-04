import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.SignedIntegerAdditionMachine

/-! # Polynomial-time canonical rational arithmetic, compiled from real machines -/
namespace PlanarHom.RationalCircuits
open Complexity BinaryArithmetic ArithmeticCircuitPrimitives
open PairProjectionMachines

/-- Finite arithmetic circuits are compiled with actual copy, pair, and sequential banks. -/
theorem fp_rational_addition : FP (BitEncoding.rat.prod BitEncoding.rat) BitEncoding.rat
    (fun p : ℚ×ℚ => p.1+p.2) := by
  have l := fp_fst BitEncoding.rat BitEncoding.rat
  have r := fp_snd BitEncoding.rat BitEncoding.rat
  have ln := l.comp fp_rat_num
  have rn := r.comp fp_rat_num
  have ld := l.comp fp_rat_den
  have rd := r.comp fp_rat_den
  have t₁ := (ln.pair (rd.comp fp_nat_int)).comp fp_int_mul
  have t₂ := (rn.pair (ld.comp fp_nat_int)).comp fp_int_mul
  have numerator := (t₁.pair t₂).comp fp_integer_addition
  have denominator := (ld.pair rd).comp fp_multiplication
  exact ((numerator.pair denominator).comp fp_rational_normalization).congr
    (fun p => by simpa only [Function.comp_apply] using (Rat.add_def' p.1 p.2).symm)

theorem fp_rational_negation : FP BitEncoding.rat BitEncoding.rat (fun q : ℚ => -q) := by
  exact (((fp_const BitEncoding.rat BitEncoding.rat (-1)).pair (fp_id BitEncoding.rat)).comp
    fp_rational_multiplication).congr (fun q => by simp)

theorem fp_rational_subtraction : FP (BitEncoding.rat.prod BitEncoding.rat) BitEncoding.rat
    (fun p : ℚ×ℚ => p.1-p.2) := by
  exact (((fp_id BitEncoding.rat).prodMap fp_rational_negation).comp fp_rational_addition).congr
    (fun p => by simp [Prod.map,sub_eq_add_neg])

theorem rational_inverse_formula (q : ℚ) :
    mkRat ((if (intParts q.num).1 then (-1:ℤ) else 1) * (q.den:ℤ)) q.num.natAbs = q⁻¹ := by
  rw [Rat.inv_def,Rat.mkRat_eq_divInt,Rat.divInt_eq_div,Rat.divInt_eq_div]
  cases h : q.num with
  | ofNat n => simp [intParts]
  | negSucc n =>
    simp only [intParts, ↓reduceIte, Int.natAbs_negSucc,
      Int.cast_mul,Int.cast_neg,Int.cast_one,Int.cast_natCast,Int.cast_negSucc]
    rw [div_neg]
    ring

/-- Total inverse, including the canonical zero result for a zero numerator. -/
theorem fp_rational_inverse : FP BitEncoding.rat BitEncoding.rat (fun q : ℚ => q⁻¹) := by
  have sign := (fp_rat_num.comp fp_int_parts).comp (fp_fst BitEncoding.bool BitEncoding.nat)
  have factor := sign.comp (fp_bool_unary BitEncoding.int (fun s => if s then (-1:ℤ) else 1))
  have numerator := (factor.pair (fp_rat_den.comp fp_nat_int)).comp fp_int_mul
  have denominator := fp_rat_num.comp fp_int_natAbs
  exact ((numerator.pair denominator).comp fp_rational_normalization).congr rational_inverse_formula

theorem fp_rational_division : FP (BitEncoding.rat.prod BitEncoding.rat) BitEncoding.rat
    (fun p : ℚ×ℚ => p.1/p.2) := by
  exact (((fp_id BitEncoding.rat).prodMap fp_rational_inverse).comp fp_rational_multiplication).congr
    (fun p => by simp [Prod.map,div_eq_mul_inv])

theorem fp_nat_isZero : FP BitEncoding.nat BitEncoding.bool (fun n : ℕ => decide (n=0)) := by
  exact (((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 1)).comp
    fp_comparison).congr (fun n => by simp [Nat.lt_one_iff])

theorem fp_integer_isZero : FP BitEncoding.int BitEncoding.bool (fun z : ℤ => decide (z=0)) := by
  exact (fp_int_natAbs.comp fp_nat_isZero).congr (fun z => by simp)

theorem fp_rational_isZero : FP BitEncoding.rat BitEncoding.bool (fun q : ℚ => decide (q=0)) := by
  exact (fp_rat_num.comp fp_integer_isZero).congr (fun q => by simp [Rat.num_eq_zero])

/-- Equality tests canonical exact values, with no numerical approximation. -/
theorem fp_rational_equality : FP (BitEncoding.rat.prod BitEncoding.rat) BitEncoding.bool
    (fun p : ℚ×ℚ => decide (p.1=p.2)) := by
  exact (fp_rational_subtraction.comp fp_rational_isZero).congr (fun p => by simp [sub_eq_zero])

theorem fp_integer_negation : FP BitEncoding.int BitEncoding.int (fun z : ℤ => -z) := by
  exact (((fp_const BitEncoding.int BitEncoding.int (-1)).pair (fp_id BitEncoding.int)).comp
    fp_int_mul).congr (fun z => by simp)

theorem fp_integer_subtraction : FP (BitEncoding.int.prod BitEncoding.int) BitEncoding.int
    (fun p : ℤ×ℤ => p.1-p.2) := by
  exact (((fp_id BitEncoding.int).prodMap fp_integer_negation).comp fp_integer_addition).congr
    (fun p => by simp [Prod.map,sub_eq_add_neg])

theorem fp_integer_equality : FP (BitEncoding.int.prod BitEncoding.int) BitEncoding.bool
    (fun p : ℤ×ℤ => decide (p.1=p.2)) := by
  exact (fp_integer_subtraction.comp fp_integer_isZero).congr (fun p => by simp [sub_eq_zero])

end PlanarHom.RationalCircuits
