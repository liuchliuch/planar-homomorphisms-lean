import PlanarHom.RationalNormalizationMachine
import PlanarHom.CodecSizeBounds
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Polynomial output-size bounds from explicit integer representatives

These bounds use the actual binary encodings. Canonical rational normalization
is the already proved machine, so its output-length polynomial controls reduced
numerator/denominator code sizes without assuming a unit-cost normalization step.
-/

namespace PlanarHom.EncodingSizeBounds
open Complexity MachineComposition BinaryArithmetic

/-- Binary length of any natural bounded by an exponential is linear in its exponent. -/
theorem nat_encoding_length_le_of_le_pow {m C n : ℕ} (hm : m ≤ C ^ n) :
    (BitEncoding.nat.encode m).length ≤ Nat.size C * n + 1 := by
  have hC : C ≤ 2 ^ Nat.size C := (Nat.lt_size_self C).le
  have hp : C ^ n ≤ 2 ^ (Nat.size C * n) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hC n
  change (Computability.encodeNat m).length ≤ _
  rw [encodeNat_length]
  exact (Nat.size_le_size (hm.trans hp)).trans_eq Nat.size_pow

/-- The sign tag and nested codec framing add only three bits to the magnitude index. -/
theorem int_encoding_length_le (z : ℤ) :
    (BitEncoding.int.encode z).length ≤ Nat.size z.natAbs + 3 := by
  cases z with
  | ofNat n =>
    simp [BitEncoding.int, BitEncoding.retract, BitEncoding.prod_length,
      BitEncoding.bool, BitEncoding.nat, encodeNat_length]
    omega
  | negSucc n =>
    have h : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (Nat.le_succ n)
    simp [BitEncoding.int, BitEncoding.retract, BitEncoding.prod_length,
      BitEncoding.bool, BitEncoding.nat, encodeNat_length]
    omega

/-- Signed integer representatives bounded exponentially have linear code length. -/
theorem int_encoding_length_le_of_natAbs_le_pow {z : ℤ} {C n : ℕ}
    (hz : z.natAbs ≤ C ^ n) :
    (BitEncoding.int.encode z).length ≤ Nat.size C * n + 4 := by
  have hn := nat_encoding_length_le_of_le_pow hz
  change (Computability.encodeNat z.natAbs).length ≤ _ at hn
  rw [encodeNat_length] at hn
  exact (int_encoding_length_le z).trans (by omega)

/-- The exact framed normalization-input word has a linear bound in the exponent. -/
theorem rational_input_length_le {z : ℤ} {d C D n : ℕ}
    (hz : z.natAbs ≤ C ^ n) (hd : d ≤ D ^ n) :
    ((BitEncoding.int.prod BitEncoding.nat).encode (z, d)).length ≤
      (2 * Nat.size C + Nat.size D) * n + 10 := by
  rw [BitEncoding.prod_length]
  have hi := int_encoding_length_le_of_natAbs_le_pow hz
  have hn := nat_encoding_length_le_of_le_pow hd
  nlinarith

/-- A proved polynomial bounding the actual canonical rational code. -/
noncomputable def rationalOutputPolynomial (C D : ℕ) : Polynomial ℕ :=
  (outputLengthPolynomial rationalNormalizationComputable).comp
    (Polynomial.C (2 * Nat.size C + Nat.size D) * Polynomial.X + Polynomial.C 10)

/-- Reduction to canonical Rat.num/Rat.den is a real bit algorithm and therefore
preserves a polynomial code bound for exponentially bounded representatives. -/
theorem rational_encoding_length_le {z : ℤ} {d C D n : ℕ}
    (hz : z.natAbs ≤ C ^ n) (hd : d ≤ D ^ n) :
    (BitEncoding.rat.encode (mkRat z d)).length ≤ (rationalOutputPolynomial C D).eval n := by
  have hout := encoded_output_length_le rationalNormalizationComputable (z, d)
  have hin := rational_input_length_le hz hd
  apply hout.trans
  have hm := natPolynomial_monotone (outputLengthPolynomial rationalNormalizationComputable) hin
  simpa [rationalOutputPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, BitEncoding.toFinEncoding] using hm

/-- Exact vector framing overhead, including the binary dimension header. -/
theorem rational_vector_length_le {dimension n : ℕ} (x : Fin dimension → ℚ)
    (h : ∀ i, (BitEncoding.rat.encode (x i)).length ≤ n) :
    ((rationalCoordinates dimension).encode x).length ≤
      2 * Nat.size dimension + 1 + 2 * dimension * n + dimension := by
  simp only [rationalCoordinates, BitEncoding.vector, BitEncoding.list,
    List.length_append, BitEncoding.frame_length, BitEncoding.frames_length,
    List.length_ofFn, List.map_ofFn, List.sum_ofFn]
  change 2 * (Computability.encodeNat dimension).length + 1 +
    (2 * (∑ i, (BitEncoding.rat.encode (x i)).length) + dimension) ≤ _
  rw [encodeNat_length]
  have hs : ∑ i, (BitEncoding.rat.encode (x i)).length ≤ dimension * n := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  nlinarith

/-- A fixed number of rational coordinates has a fixed polynomial length bound. -/
noncomputable def coordinateOutputPolynomial (dimension C D : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * Nat.size dimension + 1 + dimension) +
    Polynomial.C (2 * dimension) * rationalOutputPolynomial C D

/-- Uniform common-denominator representatives give a polynomial vector-code bound. -/
theorem rational_coordinates_length_le {dimension C D n : ℕ}
    (x : Fin dimension → ℚ)
    (h : ∀ i, ∃ z : ℤ, ∃ d : ℕ,
      x i = mkRat z d ∧ z.natAbs ≤ C ^ n ∧ d ≤ D ^ n) :
    ((rationalCoordinates dimension).encode x).length ≤
      (coordinateOutputPolynomial dimension C D).eval n := by
  have hc (i : Fin dimension) : (BitEncoding.rat.encode (x i)).length ≤
      (rationalOutputPolynomial C D).eval n := by
    obtain ⟨z, d, hx, hz, hd⟩ := h i
    rw [hx]
    exact rational_encoding_length_le hz hd
  have hv := rational_vector_length_le x hc
  simpa [coordinateOutputPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv

end PlanarHom.EncodingSizeBounds
