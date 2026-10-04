import PlanarHom.RationalCircuits

/-! # Canonical rational order tests from the actual numerator sign bit -/
namespace PlanarHom.RationalOrderMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines RationalCircuits

theorem fp_integer_negative : FP BitEncoding.int BitEncoding.bool
    (fun z : ℤ => decide (z < 0)) := by
  exact (fp_int_parts.comp (fp_fst BitEncoding.bool BitEncoding.nat)).congr
    (fun z => by cases z <;> simp [intParts])

theorem fp_negative : FP BitEncoding.rat BitEncoding.bool
    (fun q : ℚ => decide (q < 0)) := by
  exact (fp_rat_num.comp fp_integer_negative).congr
    (fun q => by simp only [Function.comp_apply, ← not_le, Rat.num_nonneg])

theorem fp_nonnegative : FP BitEncoding.rat BitEncoding.bool
    (fun q : ℚ => decide (0 ≤ q)) := by
  exact (fp_negative.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr
    (fun q => by
      by_cases h : q < 0
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h])

theorem fp_positive : FP BitEncoding.rat BitEncoding.bool
    (fun q : ℚ => decide (0 < q)) := by
  exact (fp_rational_negation.comp fp_negative).congr (fun q => by simp)

end PlanarHom.RationalOrderMachines
