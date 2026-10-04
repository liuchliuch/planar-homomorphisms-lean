import PlanarHom.AlphabetCoordinateCertificates
import PlanarHom.LagrangeCoefficientHeights

/-! Exact common-denominator certificates for Lagrange numerators and denominators. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.FieldCoordinateCertificates
open IntegerCoordinateBounds LagrangeCoefficientHeights

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}
namespace Certificate

/-- Transporting a certificate does not alter its bounds. -/
theorem bounded_congr {x y : K} (h : x = y) (a : Certificate basis x) {N D : ℕ}
    (ha : a.Bounded N D) : (congr h a).Bounded N D := by
  cases h
  exact ha

/-- Difference uses actual addition and negation certificates. -/
def sub {x y : K} (a : Certificate basis x) (b : Certificate basis y) : Certificate basis (x - y) :=
  congr (sub_eq_add_neg x y).symm (a.add b.neg)

theorem bounded_sub_uniform {x y : K} (a : Certificate basis x) (b : Certificate basis y)
    {H : ℕ} (ha : a.Bounded H H) (hb : b.Bounded H H) :
    (a.sub b).Bounded (2 * H ^ 2) (2 * H ^ 2) := by
  apply bounded_congr _ _
  apply bounded_mono _ (bounded_add a b.neg ha (bounded_neg b hb))
  · nlinarith
  · nlinarith

/-- Exact Lagrange denominator, including the extra node factor for shifted queries. -/
def lagrangeDenominator {J : Type} (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (μ : J → K) (a : ∀ j, Certificate basis (μ j)) (j : J) (others : List J) :
    Certificate basis (μ j * (others.map (fun k => μ j - μ k)).prod) :=
  (a j).mul data (product data (fun k => μ j - μ k) (fun k => (a j).sub (a k)) others)

/-- Explicit uniform representative height before inversion. -/
def lagrangeDenominatorBound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k)) (H n : ℕ) : ℕ :=
  heightConstant data * H * (heightConstant data * (2 * H ^ 2)) ^ (n + 1)

theorem lagrangeDenominator_bounded {J : Type}
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (μ : J → K) (a : ∀ j, Certificate basis (μ j)) (j : J) (others : List J) {H : ℕ}
    (hH : 1 ≤ H) (ha : ∀ k, (a k).Bounded H H) :
    (lagrangeDenominator data μ a j others).Bounded (lagrangeDenominatorBound data H others.length)
      (lagrangeDenominatorBound data H others.length) := by
  apply bounded_mul_uniform data (a j) _ (ha j)
  apply product_bounded
  · nlinarith
  · intro k
    exact bounded_sub_uniform (a j) (a k) (ha j) (ha k)

omit [Algebra ℚ K] in
/-- Distinct nonzero retained nodes give the actual needed nonzero denominator. -/
theorem lagrangeDenominator_ne_zero {J : Type} (μ : J → K) (hμ : Function.Injective μ)
    (j : J) (hj : μ j ≠ 0) (others : List J) (hothers : ∀ k ∈ others, k ≠ j) :
    μ j * (others.map (fun k => μ j - μ k)).prod ≠ 0 := by
  apply mul_ne_zero hj
  apply List.prod_ne_zero
  intro hv
  obtain ⟨k, hk, hz⟩ := List.mem_map.mp hv
  exact (sub_ne_zero.mpr (fun h => hothers k hk (hμ h).symm)) hz

/-- Inverting the actual Lagrange denominator has a fixed-degree height bound. -/
theorem lagrangeInverse_bounded {J : Type}
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (μ : J → K) (a : ∀ j, Certificate basis (μ j)) (j : J) (others : List J)
    (hzero : μ j * (others.map (fun k => μ j - μ k)).prod ≠ 0) {H : ℕ}
    (hH : 1 ≤ H) (ha : ∀ k, (a k).Bounded H H) :
    ((lagrangeDenominator data μ a j others).inv data hzero).Bounded
      (inverseHeightBound data (lagrangeDenominatorBound data H others.length)
        (lagrangeDenominatorBound data H others.length))
      (inverseHeightBound data (lagrangeDenominatorBound data H others.length)
        (lagrangeDenominatorBound data H others.length)) :=
  bounded_inv data _ hzero (lagrangeDenominator_bounded data μ a j others hH ha)

/-- Coefficient certificates preserve the shared denominator of all Boolean expansion terms. -/
def lagrangeCoefficient {ι : Type} [Fintype ι] (A : ι → K)
    (data : ClearedCoordinates basis (extendedValue A)) {N : ℕ}
    (m : ℕ) (words : Fin N → List ι) (hlen : ∀ i, (words i).length = m) (k : ℕ) :
    Certificate basis ((∏ i, (Polynomial.X - Polynomial.C (((words i).map A).prod))).coeff k) :=
  congr (coefficient_eq_sum_words A m words k).symm
    (sumWords data (coefficientWord m words k) (N * (m + 1) + 1)
      (coefficientWord_length m words hlen k))

theorem lagrangeCoefficient_bounded {ι : Type} [Fintype ι] (A : ι → K)
    (data : ClearedCoordinates basis (extendedValue A)) {N : ℕ}
    (m : ℕ) (words : Fin N → List ι) (hlen : ∀ i, (words i).length = m) (k : ℕ) :
    (lagrangeCoefficient A data m words hlen k).Bounded
      ((2 * growthConstant data) ^ (N * (m + 1) + 1 + 1))
      (data.denominator ^ (N * (m + 1) + 1 + 1)) := by
  apply bounded_congr
  apply sumWords_bounded_exponential
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  apply Nat.pow_le_pow_right (by omega)
  nlinarith

end Certificate
end PlanarHom.FieldCoordinateCertificates
