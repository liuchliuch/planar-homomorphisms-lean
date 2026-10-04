import PlanarHom.BiasedBinaryRealEmbedding
import Mathlib.RingTheory.Norm.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-! A fixed rational prime separates the occupied-degree statistic in a real
number field. This converts the joint-product gate into a single interaction
product after attaching the available unary (1,p) at both edge endpoints. -/
namespace PlanarHom.BiasedBinaryProductSeparation

private theorem rational_valuation_zero (q : ℚ) (hq : q≠0) (p : ℕ)
    (hn : q.num.natAbs<p) (hd : q.den<p) : padicValRat p q=0 := by
  unfold padicValRat padicValInt
  rw [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt
      (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq)) hn),
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt q.den_pos hd)]
  simp

/-- The prime is fixed by the three coefficients, independent of the input. -/
theorem exists_common_unit_prime (a b c : ℚ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    ∃ p : ℕ,p.Prime ∧ padicValRat p a=0 ∧ padicValRat p b=0 ∧ padicValRat p c=0 := by
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes
    (a.num.natAbs+a.den+b.num.natAbs+b.den+c.num.natAbs+c.den+1)
  refine ⟨p,hprime,rational_valuation_zero a ha p (by omega) (by omega),
    rational_valuation_zero b hb p (by omega) (by omega),
    rational_valuation_zero c hc p (by omega) (by omega)⟩

variable {K : Type*} [Field K] [Algebra ℚ K] [Module.Finite ℚ K]

theorem exists_norm_unit_prime (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    ∃ p : ℕ,p.Prime ∧ padicValRat p (Algebra.norm ℚ a)=0 ∧
      padicValRat p (Algebra.norm ℚ b)=0 ∧ padicValRat p (Algebra.norm ℚ c)=0 :=
  exists_common_unit_prime _ _ _ (Algebra.norm_ne_zero_iff.mpr ha)
    (Algebra.norm_ne_zero_iff.mpr hb) (Algebra.norm_ne_zero_iff.mpr hc)

namespace EdgeCounts

theorem normalized_product (s : EdgeCounts) (a b c p : K) :
    s.product a (b*p) (c*p^2)=s.product a b c*p^s.occupiedDegree := by
  simp only [product,occupiedDegree,mul_pow,pow_add,pow_mul]
  ring

/-- Taking the p-adic valuation after the field norm reads the occupied degree
of the normalized interaction exactly, scaled by the fixed field dimension. -/
theorem normalized_norm_valuation (s : EdgeCounts) (a b c : K) (p : ℕ)
    (hp : p.Prime) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hva : padicValRat p (Algebra.norm ℚ a)=0)
    (hvb : padicValRat p (Algebra.norm ℚ b)=0)
    (hvc : padicValRat p (Algebra.norm ℚ c)=0) :
    padicValRat p (Algebra.norm ℚ (s.product a (b*(p:K)) (c*(p:K)^2)))=
      (s.occupiedDegree : ℤ)*(Module.finrank ℚ K : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hna : Algebra.norm ℚ a≠0 := Algebra.norm_ne_zero_iff.mpr ha
  have hnb : Algebra.norm ℚ b≠0 := Algebra.norm_ne_zero_iff.mpr hb
  have hnc : Algebra.norm ℚ c≠0 := Algebra.norm_ne_zero_iff.mpr hc
  have hpq : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hnp : Algebra.norm ℚ (p:K)=(p:ℚ)^Module.finrank ℚ K := by
    rw [← map_natCast (algebraMap ℚ K),Algebra.norm_algebraMap]
  rw [normalized_product]
  simp only [product,map_mul,map_pow,hnp]
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hna)
      (pow_ne_zero _ hnb)) (pow_ne_zero _ hnc))
      (pow_ne_zero _ (pow_ne_zero _ hpq)),
    padicValRat.mul (mul_ne_zero (pow_ne_zero _ hna) (pow_ne_zero _ hnb)) (pow_ne_zero _ hnc),
    padicValRat.mul (pow_ne_zero _ hna) (pow_ne_zero _ hnb)]
  simp only [padicValRat.pow hna,padicValRat.pow hnb,padicValRat.pow hnc,
    padicValRat.pow (pow_ne_zero _ hpq),padicValRat.pow hpq,padicValRat.self hp.one_lt,
    hva,hvb,hvc,mul_zero,zero_add,mul_one]

/-- Equality of the one normalized source product already forces equal degree. -/
theorem degree_eq_of_normalized_product (s t : EdgeCounts) (a b c : K) (p : ℕ)
    (hp : p.Prime) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hva : padicValRat p (Algebra.norm ℚ a)=0)
    (hvb : padicValRat p (Algebra.norm ℚ b)=0)
    (hvc : padicValRat p (Algebra.norm ℚ c)=0)
    (he : s.product a (b*(p:K)) (c*(p:K)^2)=t.product a (b*(p:K)) (c*(p:K)^2)) :
    s.occupiedDegree=t.occupiedDegree := by
  have hv := congrArg (fun x : K => padicValRat p (Algebra.norm ℚ x)) he
  dsimp only at hv
  rw [normalized_norm_valuation s a b c p hp ha hb hc hva hvb hvc,
    normalized_norm_valuation t a b c p hp ha hb hc hva hvb hvc] at hv
  have hd : (Module.finrank ℚ K : ℤ)≠0 := by
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos (R:=ℚ) (M:=K)))
  exact_mod_cast mul_right_cancel₀ hd hv
end EdgeCounts
end PlanarHom.BiasedBinaryProductSeparation
