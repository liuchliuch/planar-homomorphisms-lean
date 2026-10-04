import PlanarHom.SparseMatrixLeading

/-!
# Exponential monomial identities preserve distance-kernel monomials

This is the analytic relation check in Lemma 4.2(iv). Positive shortest-distance
leading coefficients imply that equal products of actual exponential entries
have equal total graph-distance exponents. Hence their distance-kernel products
agree for every target parameter.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients

/-- A finite product has coefficient equal to the product of coefficients and
order equal to the sum of orders. -/
theorem finset_prod_leading_isBigO {I : Type*} (S : Finset I)
    (f : I → ℝ → ℝ) (a : I → ℝ) (n : I → ℕ)
    (hf : ∀ i ∈ S, (fun t => f i t - a i * t ^ n i) =O[𝓝 0]
      (fun t : ℝ => t ^ (n i + 1))) :
    (fun t => (∏ i ∈ S, f i t) - (∏ i ∈ S, a i) * t ^ (∑ i ∈ S, n i)) =O[𝓝 0]
      (fun t : ℝ => t ^ ((∑ i ∈ S, n i) + 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | @insert i S hi ih =>
    have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have h := mul_leading_isBigO (a i) (∏ j ∈ S, a j) (n i) (∑ j ∈ S, n j)
      (hf i (Finset.mem_insert_self i S)) hrest
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using h

/-- Two nonzero leading coefficients for the same germ must have the same order. -/
theorem leading_order_unique {f : ℝ → ℝ} (a b : ℝ) (m n : ℕ)
    (hane : a ≠ 0) (hbne : b ≠ 0)
    (ha : (fun t => f t - a * t ^ m) =O[𝓝 0] (fun t : ℝ => t ^ (m + 1)))
    (hb : (fun t => f t - b * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) : m = n := by
  by_contra hmn
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · have hz := (isBigO_of_leading b n hb).trans (pow_isBigO_pow hlt)
    have hzero : (fun t => f t - 0 * t ^ m) =O[𝓝 0] (fun t : ℝ => t ^ (m + 1)) := by
      simpa only [zero_mul, sub_zero] using hz
    exact hane (leading_coefficient_unique a 0 m ha hzero)
  · have hz := (isBigO_of_leading a m ha).trans (pow_isBigO_pow hgt)
    have hzero : (fun t => f t - 0 * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1)) := by
      simpa only [zero_mul, sub_zero] using hz
    exact hbne (leading_coefficient_unique b 0 n hb hzero)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite product of exponential entries has an explicit coefficient at
the sum of graph distances, with an error of one higher order. -/
theorem exp_entry_product_leading_isBigO (L : Matrix V V ℝ) (hL : L.IsHermitian)
    {I : Type*} [Fintype I] (e : I → V × V) :
    let G := LogarithmicSupport.offDiagonalSupport L hL
    let a := fun k => (L ^ G.dist (e k).1 (e k).2) (e k).1 (e k).2 /
      ((G.dist (e k).1 (e k).2).factorial : ℝ)
    (fun t => (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) -
      (∏ k, a k) * t ^ (∑ k, G.dist (e k).1 (e k).2)) =O[𝓝 0]
      (fun t : ℝ => t ^ ((∑ k, G.dist (e k).1 (e k).2) + 1)) := by
  apply finset_prod_leading_isBigO
  intro k hk
  exact exp_entry_distance_leading_isBigO L hL (e k).1 (e k).2

/-- Equality of actual exponential-entry products forces equality of their
sum of distances. It is enough that the products agree in a neighborhood of zero. -/
theorem exp_product_identity_sum_dist_eq (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    {I J : Type*} [Fintype I] [Fintype J] (e : I → V × V) (f : J → V × V)
    (heq : ∀ᶠ (t : ℝ) in 𝓝 0,
      (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) =
      ∏ k, NormedSpace.exp ℝ (t • L) (f k).1 (f k).2) :
    (∑ k, (LogarithmicSupport.offDiagonalSupport L hL).dist (e k).1 (e k).2) =
      ∑ k, (LogarithmicSupport.offDiagonalSupport L hL).dist (f k).1 (f k).2 := by
  let G := LogarithmicSupport.offDiagonalSupport L hL
  let a := fun (p : V × V) => (L ^ G.dist p.1 p.2) p.1 p.2 / ((G.dist p.1 p.2).factorial : ℝ)
  have hpos : ∀ p, 0 < a p := fun p =>
    exp_distance_leading_coefficient_pos L hL hG hedge p.1 p.2
  have hleft := exp_entry_product_leading_isBigO L hL e
  have hright := exp_entry_product_leading_isBigO L hL f
  have hright' :
      (fun t => (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) -
        (∏ k, a (f k)) * t ^ (∑ k, G.dist (f k).1 (f k).2)) =O[𝓝 0]
      (fun t : ℝ => t ^ ((∑ k, G.dist (f k).1 (f k).2) + 1)) := by
    apply hright.congr'
    · filter_upwards [heq] with t ht
      rw [ht]
    · rfl
  exact leading_order_unique (∏ k, a (e k)) (∏ k, a (f k)) _ _
    (ne_of_gt (Finset.prod_pos fun k _ => hpos (e k)))
    (ne_of_gt (Finset.prod_pos fun k _ => hpos (f k))) hleft hright'

/-- The target distance kernel preserves every source exponential monomial
identity, exactly as required by the interpolation lemma's relation test. -/
theorem distanceKernel_products_eq_of_exp_products_eq (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    {I J : Type*} [Fintype I] [Fintype J] (e : I → V × V) (f : J → V × V)
    (heq : ∀ᶠ (t : ℝ) in 𝓝 0,
      (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) =
      ∏ k, NormedSpace.exp ℝ (t • L) (f k).1 (f k).2) (x : ℝ) :
    (∏ k, EntropyCompletion.distanceKernel (LogarithmicSupport.offDiagonalSupport L hL) x
      (e k).1 (e k).2) =
    ∏ k, EntropyCompletion.distanceKernel (LogarithmicSupport.offDiagonalSupport L hL) x
      (f k).1 (f k).2 := by
  simp only [EntropyCompletion.distanceKernel, Matrix.of_apply, Finset.prod_pow_eq_pow_sum]
  rw [exp_product_identity_sum_dist_eq L hL hG hedge e f heq]

end PlanarHom.MatrixLogCoefficients
