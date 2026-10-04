import PlanarHom.NaturalPowerRootMachines
import Mathlib.Data.Rat.Cast.Order

/-! # Canonical rational positive power roots without an oracle

The numerator and denominator of a power of a reduced rational are themselves
the corresponding integer powers. Two concrete binary bisection machines
therefore recover any promised nonnegative rational root exactly.
-/

namespace PlanarHom.RationalPowerRoot
open Complexity BinaryArithmetic ArithmeticCircuitPrimitives

def root (n : ℕ) (q : ℚ) : ℚ :=
  mkRat (NaturalPowerRoot.root n q.num.natAbs) (NaturalPowerRoot.root n q.den)

theorem root_pow (n : ℕ) (hn : n ≠ 0) (q : ℚ) (hq : 0 ≤ q) :
    root n (q^n) = q := by
  unfold root
  rw [Rat.num_pow, Rat.den_pow, Int.natAbs_pow,
    NaturalPowerRoot.root_pow n hn, NaturalPowerRoot.root_pow n hn]
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  rw [Int.natCast_natAbs, abs_of_nonneg hnum]
  exact Rat.mkRat_self q

/-- Two actual natural-root machines followed by the canonical normalization
machine. This theorem is unconditional; correctness as a positive root is the
separate promise theorem `root_pow`. -/
theorem fp_root (n : ℕ) : FP BitEncoding.rat BitEncoding.rat (root n) := by
  have hn := (((fp_rat_num.comp fp_int_natAbs).comp (NaturalPowerRoot.fp_root n)).comp
    fp_nat_int)
  have hd := fp_rat_den.comp (NaturalPowerRoot.fp_root n)
  exact (hn.pair hd).comp fp_rational_normalization

end PlanarHom.RationalPowerRoot
