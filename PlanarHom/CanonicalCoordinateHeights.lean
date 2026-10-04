import PlanarHom.FieldExpressionHeights
import PlanarHom.CoefficientListHeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exponential coordinate representatives controlled by the actual canonical input length. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.CanonicalCoordinateHeights
open Complexity BinaryArithmetic FieldCoordinateCertificates

/-- A canonical natural code represents a value below the corresponding power of two. -/
theorem nat_le_pow_encoding_length (n : ℕ) : n ≤ 2 ^ (BitEncoding.nat.encode n).length := by
  change n ≤ 2 ^ (Computability.encodeNat n).length
  rw [encodeNat_length]
  exact (Nat.lt_size_self n).le

/-- The signed-index integer code bounds the absolute numerator as well. -/
theorem int_natAbs_le_pow_encoding_length (z : ℤ) :
    z.natAbs ≤ 2 ^ (BitEncoding.int.encode z).length := by
  cases z with
  | ofNat n =>
    have hn := Nat.lt_size_self n
    simp only [BitEncoding.int, BitEncoding.retract, BitEncoding.prod_length,
      BitEncoding.bool, List.length_singleton, BitEncoding.nat, encodeNat_length, Int.natAbs_natCast]
    exact hn.le.trans (Nat.pow_le_pow_right (by omega) (by omega))
  | negSucc n =>
    have hn := Nat.lt_size_self n
    simp only [BitEncoding.int, BitEncoding.retract, BitEncoding.prod_length,
      BitEncoding.bool, List.length_singleton, BitEncoding.nat, encodeNat_length, Int.natAbs_negSucc]
    exact (Nat.succ_le_of_lt hn).trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- Canonical rational numerator and denominator heights are bounded by their serialized length. -/
theorem rat_heights_le_pow_encoding_length (x : ℚ) :
    x.num.natAbs ≤ 2 ^ (BitEncoding.rat.encode x).length ∧
    x.den ≤ 2 ^ (BitEncoding.rat.encode x).length := by
  have hnum := int_natAbs_le_pow_encoding_length x.num
  have hden := nat_le_pow_encoding_length x.den
  have hlen : (BitEncoding.rat.encode x).length =
      2 * (BitEncoding.int.encode x.num).length + (BitEncoding.nat.encode x.den).length + 1 := by
    exact BitEncoding.prod_length _ _ _
  constructor
  · exact hnum.trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact hden.trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- One coordinate's canonical rational word is charged by the field vector code. -/
theorem coordinate_encoding_length_le {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (x : K) (i : Fin dimension) :
    (BitEncoding.rat.encode (basis.equivFun x i)).length ≤ ((numberFieldEncoding basis).encode x).length := by
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin dimension => (BitEncoding.rat.encode (basis.equivFun x j)).length)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simp only [numberFieldEncoding, BitEncoding.retract, rationalCoordinates, BitEncoding.vector,
    BitEncoding.list, List.length_append, BitEncoding.frame_length, BitEncoding.frames_length,
    List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  dsimp only at hs
  omega

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- Clear all canonical coordinate denominators together, without any arithmetic oracle. -/
def certificate (basis : Module.Basis (Fin dimension) ℚ K) (x : K) : Certificate basis x where
  denominator := ∏ i, (basis.equivFun x i).den
  denominator_pos := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Rat.den_pos _).ne'))
  numerator := fun i => (basis.equivFun x i).num *
    ((∏ j ∈ Finset.univ.erase i, (basis.equivFun x j).den : ℕ) : ℤ)
  spec := by
    intro i
    have hp := Finset.prod_erase_mul Finset.univ (fun j => (basis.equivFun x j).den)
      (Finset.mem_univ i)
    rw [← hp, Nat.cast_mul]
    conv_lhs => rhs; rw [← Rat.num_div_den (basis.equivFun x i)]
    have hd : ((basis.equivFun x i).den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos _).ne'
    push_cast
    field_simp

/-- Uniform coordinate height yields a bounded shared-denominator certificate. -/
theorem certificate_bounded_of_coordinates (basis : Module.Basis (Fin dimension) ℚ K) (x : K)
    (H : ℕ) (hH : 0 < H)
    (h : ∀ i, (basis.equivFun x i).num.natAbs ≤ H ∧ (basis.equivFun x i).den ≤ H) :
    (certificate basis x).Bounded (H ^ (dimension + 1)) (H ^ (dimension + 1)) := by
  have hp (s : Finset (Fin dimension)) :
      (∏ j ∈ s, (basis.equivFun x j).den) ≤ H ^ s.card := by
    simpa using Finset.prod_le_prod' (s := s) (fun j _ => (h j).2)
  have hd : (∏ i, (basis.equivFun x i).den) ≤ H ^ dimension := by simpa using hp Finset.univ
  refine ⟨hd.trans (Nat.pow_le_pow_right hH (Nat.le_succ _)), fun i => ?_⟩
  change ((basis.equivFun x i).num *
    ((∏ j ∈ Finset.univ.erase i, (basis.equivFun x j).den : ℕ) : ℤ)).natAbs ≤ _
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    (basis.equivFun x i).num.natAbs * (∏ j ∈ Finset.univ.erase i, (basis.equivFun x j).den) ≤
        H * H ^ (Finset.univ.erase i).card := Nat.mul_le_mul (h i).1 (hp _)
    _ ≤ H * H ^ dimension := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hH
      (by simpa using (Finset.card_erase_le (s := Finset.univ) (a := i))))
    _ = _ := (pow_succ' H dimension).symm

/-- Every encoded field input admits exponentially bounded exact coordinate representatives. -/
theorem certificate_bounded_by_input (basis : Module.Basis (Fin dimension) ℚ K) (x : K)
    (N : ℕ) (hx : ((numberFieldEncoding basis).encode x).length ≤ N) :
    (certificate basis x).Bounded ((2 ^ (dimension + 1)) ^ N) ((2 ^ (dimension + 1)) ^ N) := by
  have h (i : Fin dimension) : (basis.equivFun x i).num.natAbs ≤ 2 ^ N ∧
      (basis.equivFun x i).den ≤ 2 ^ N := by
    have hi := (coordinate_encoding_length_le basis x i).trans hx
    have hb := rat_heights_le_pow_encoding_length (basis.equivFun x i)
    exact ⟨hb.1.trans (Nat.pow_le_pow_right (by omega) hi),
      hb.2.trans (Nat.pow_le_pow_right (by omega) hi)⟩
  have hc := certificate_bounded_of_coordinates basis x (2 ^ N) (pow_pos (by omega) _) h
  rw [← pow_mul, Nat.mul_comm N (dimension + 1), pow_mul] at hc
  exact hc

end PlanarHom.CanonicalCoordinateHeights
