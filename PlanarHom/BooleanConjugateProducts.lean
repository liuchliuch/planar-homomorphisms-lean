import PlanarHom.BooleanRatioIndependence
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Nonvanishing of the genuine spectral-product conjugates

All square roots below are the positive real square root. A Boolean sign swaps
both branches within one parameter class. Integer-power ratio independence
rules out an identity between products with a differing unequal-diagonal
count. Analyticity on the connected oracle interval then rules out an
identically zero finite product of such conjugate differences.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace PlanarHom.BooleanConjugateProducts
open BooleanEigenvalueBranches BooleanRatioParity BooleanRatioIndependence
open BooleanSquareRootIndependence

/-- `false` is the larger branch and `true` the smaller branch. -/
def signedBranch (σ : Bool) (c a w x : ℝ) : ℝ :=
  if σ then minus c a w (x^2) else plus c a w (x^2)

/-- The branch agrees literally with changing the sign of the square root. -/
theorem signedBranch_eq_add_signedRoot (σ : Bool) (c a w x : ℝ) :
    signedBranch σ c a w x =
      c + (if σ then -Real.sqrt (a^2+w^2*x^2) else Real.sqrt (a^2+w^2*x^2)) := by
  cases σ <;> simp [signedBranch, plus, minus, root, sub_eq_add_neg]

/-- The paired branch receives the opposite square-root sign. -/
theorem signedBranch_not_eq_sub_signedRoot (σ : Bool) (c a w x : ℝ) :
    signedBranch (!σ) c a w x =
      c - (if σ then -Real.sqrt (a^2+w^2*x^2) else Real.sqrt (a^2+w^2*x^2)) := by
  cases σ <;> simp [signedBranch, plus, minus, root]

/-- The counts `k` count the smaller branches before applying the sign choice. -/
def spectralProduct {ι : Type*} (s : Finset ι) (c a w : ι → ℝ)
    (n k : ι → ℕ) (σ : ι → Bool) (x : ℝ) : ℝ :=
  ∏ i ∈ s, signedBranch (σ i) (c i) (a i) (w i) x ^ (n i-k i) *
    signedBranch (!(σ i)) (c i) (a i) (w i) x ^ k i

/-- The actual radicand is positive everywhere on the oracle interval,
including the equal-diagonal case `a = 0`. -/
theorem radicand_pos {a w x : ℝ} (hw : 0 < w) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < a^2+w^2*x^2 := by
  have := mul_pos (sq_pos_of_pos hw) (sq_pos_of_pos hx.1)
  nlinarith [sq_nonneg a]

theorem branch_pos (σ : Bool) {c a w x : ℝ} (hc : 0 < c) (hca : c^2-a^2=1)
    (hw : 0 < w) (hw1 : w < 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < signedBranch σ c a w x := by
  have hb := branches_positive c a w (x^2) hc hca (radicand_pos hw hx)
    (square_parameter_bounds hw hw1 ⟨by linarith [hx.1], hx.2⟩)
  cases σ <;> simp only [signedBranch, Bool.false_eq_true, ↓reduceIte] <;> tauto

theorem analyticAt_signedBranch (σ : Bool) (c a w x : ℝ)
    (hw : 0 < w) (hx : x ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (signedBranch σ c a w) x := by
  have hr : AnalyticAt ℝ (fun y : ℝ => root a w (y^2)) x :=
    AnalyticAt.sqrt_pos (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2)))
      (radicand_pos hw hx)
  cases σ
  · exact analyticAt_const.add hr
  · exact analyticAt_const.sub hr

theorem analyticOnNhd_spectralProduct {ι : Type*} (s : Finset ι) (c a w : ι → ℝ)
    (n k : ι → ℕ) (σ : ι → Bool) (hw : ∀ i ∈ s, 0 < w i) :
    AnalyticOnNhd ℝ (spectralProduct s c a w n k σ) (Ioo (0 : ℝ) 1) := by
  intro x hx
  apply s.analyticAt_fun_prod
  intro i hi
  exact ((analyticAt_signedBranch _ _ _ _ _ (hw i hi) hx).pow (n i-k i)).mul
    ((analyticAt_signedBranch _ _ _ _ _ (hw i hi) hx).pow (k i))

theorem spectralProduct_pos {ι : Type*} (s : Finset ι) (c a w : ι → ℝ)
    (n k : ι → ℕ) (σ : ι → Bool) (x : ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < spectralProduct s c a w n k σ x := by
  apply Finset.prod_pos
  intro i hi
  exact mul_pos (pow_pos (branch_pos _ (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx) _)
    (pow_pos (branch_pos _ (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx) _)

/-- Cancelling the common total exponent leaves exactly an integer power
of the smaller-to-larger branch ratio. -/
theorem monomial_div_monomial (p m : ℝ) (hp : p ≠ 0) (hm : m ≠ 0)
    (n k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) :
    (p^(n-k)*m^k)/(p^(n-l)*m^l) = (m/p)^((k : ℤ)-l) := by
  rw [pow_sub₀ p hp hk, pow_sub₀ p hp hl,
    zpow_sub₀ (div_ne_zero hm hp), zpow_natCast, zpow_natCast, div_pow, div_pow]
  field_simp

/-- Sign reversal negates the count difference. -/
def signedExponent (σ : Bool) (k l : ℕ) : ℤ :=
  if σ then (l : ℤ)-k else (k : ℤ)-l

theorem signedExponent_ne_zero (σ : Bool) {k l : ℕ} (hkl : k ≠ l) :
    signedExponent σ k l ≠ 0 := by
  cases σ <;> simp only [signedExponent, Bool.false_eq_true, ↓reduceIte, sub_ne_zero]
  · exact_mod_cast hkl
  · exact_mod_cast hkl.symm

theorem signed_monomial_div_monomial (σ : Bool) (c a w x : ℝ)
    (hp : plus c a w (x^2) ≠ 0) (hm : minus c a w (x^2) ≠ 0)
    (n k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) :
    (signedBranch σ c a w x^(n-k)*signedBranch (!σ) c a w x^k) /
      (signedBranch σ c a w x^(n-l)*signedBranch (!σ) c a w x^l) =
      ratio c a w (x^2)^signedExponent σ k l := by
  cases σ
  · exact monomial_div_monomial _ _ hp hm n k l hk hl
  · simp only [signedBranch, Bool.not_true, Bool.false_eq_true, ↓reduceIte, signedExponent]
    rw [monomial_div_monomial _ _ hm hp n k l hk hl]
    rw [show (k : ℤ)-l = -((l : ℤ)-k) by ring, zpow_neg]
    rw [← inv_zpow, inv_div]
    rfl

/-- A ratio of spectral products is a product of actual branch ratios. -/
theorem spectralProduct_div_spectralProduct {ι : Type*} (s : Finset ι)
    (c a w : ι → ℝ) (n k l : ι → ℕ) (σ : ι → Bool) (x : ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hk : ∀ i ∈ s, k i ≤ n i) (hl : ∀ i ∈ s, l i ≤ n i)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    spectralProduct s c a w n k σ x / spectralProduct s c a w n l σ x =
      ∏ i ∈ s, ratio (c i) (a i) (w i) (x^2)^signedExponent (σ i) (k i) (l i) := by
  unfold spectralProduct
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  apply signed_monomial_div_monomial _ _ _ _ _ _ _ _ _ _ (hk i hi) (hl i hi)
  · exact ne_of_gt (branch_pos false (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx)
  · exact ne_of_gt (branch_pos true (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx)

/-- Every sign conjugate of a difference with an unequal-diagonal count
change is a genuinely nonzero function on the oracle interval. -/
theorem exists_spectralProduct_sub_ne_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c a w : ι → ℝ) (n k l : ι → ℕ) (σ : ι → Bool)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hinj : Set.InjOn (fun i => (a i / w i)^2) {i | i ∈ s ∧ a i ≠ 0})
    (hk : ∀ i ∈ s, k i ≤ n i) (hl : ∀ i ∈ s, l i ≤ n i)
    (hdiff : ∃ g ∈ s, a g ≠ 0 ∧ k g ≠ l g) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      spectralProduct s c a w n k σ x - spectralProduct s c a w n l σ x ≠ 0 := by
  by_contra! hzero
  have hratio : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∏ i ∈ s, ratio (c i) (a i) (w i) (x^2)^signedExponent (σ i) (k i) (l i) = 1 := by
    intro x hx
    rw [← spectralProduct_div_spectralProduct s c a w n k l σ x hc hca hw hw1 hk hl hx,
      sub_eq_zero.mp (hzero x hx)]
    exact div_self (ne_of_gt (spectralProduct_pos s c a w n l σ x hc hca hw hw1 hx))
  have hz := ratio_product_identity_exponents_zero s c a w
    (fun i => signedExponent (σ i) (k i) (l i)) hc hca hw hw1 hinj hratio
  obtain ⟨g, hg, hag, hkl⟩ := hdiff
  exact signedExponent_ne_zero (σ g) hkl (hz g hg hag)

/-- Nonzero analytic functions on the connected oracle interval have a
nonzero finite product. This uses the analytic identity theorem, so no
common nonzero sample is assumed. -/
theorem exists_finset_prod_ne_zero {κ : Type*} (t : Finset κ) (f : κ → ℝ → ℝ)
    (ha : ∀ i ∈ t, AnalyticOnNhd ℝ (f i) (Ioo (0 : ℝ) 1))
    (hn : ∀ i ∈ t, ∃ x ∈ Ioo (0 : ℝ) 1, f i x ≠ 0) :
    ∃ x ∈ Ioo (0 : ℝ) 1, (∏ i ∈ t, f i x) ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1/2, by norm_num, by simp⟩
  | @insert i t hi ih =>
    have hat : ∀ j ∈ t, AnalyticOnNhd ℝ (f j) (Ioo (0 : ℝ) 1) :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hnt : ∀ j ∈ t, ∃ x ∈ Ioo (0 : ℝ) 1, f j x ≠ 0 :=
      fun j hj => hn j (Finset.mem_insert_of_mem hj)
    by_contra! hzero
    have hm : ∀ x ∈ Ioo (0 : ℝ) 1, f i x * (∏ j ∈ t, f j x) = 0 := by
      simpa only [Finset.prod_insert hi] using hzero
    have hz := (ha i (Finset.mem_insert_self i t)).eq_zero_or_eq_zero_of_mul_eq_zero
      (t.analyticOnNhd_fun_prod hat) hm (convex_Ioo (0 : ℝ) 1).isPreconnected
    rcases hz with hz | hz
    · obtain ⟨x, hx, hnx⟩ := hn i (Finset.mem_insert_self i t)
      exact hnx (hz x hx)
    · obtain ⟨x, hx, hnx⟩ := ih hat hnt
      exact hnx (hz x hx)

/-- Product over any finite set of branch-sign conjugates. -/
def conjugateProduct {ι : Type*} (s : Finset ι) (c a w : ι → ℝ)
    (n k l : ι → ℕ) (signs : Finset (ι → Bool)) (x : ℝ) : ℝ :=
  ∏ σ ∈ signs,
    (spectralProduct s c a w n k σ x - spectralProduct s c a w n l σ x)

theorem analyticOnNhd_conjugateProduct {ι : Type*} (s : Finset ι) (c a w : ι → ℝ)
    (n k l : ι → ℕ) (signs : Finset (ι → Bool)) (hw : ∀ i ∈ s, 0 < w i) :
    AnalyticOnNhd ℝ (conjugateProduct s c a w n k l signs) (Ioo (0 : ℝ) 1) := by
  apply signs.analyticOnNhd_fun_prod
  intro σ _
  exact (analyticOnNhd_spectralProduct s c a w n k σ hw).sub
    (analyticOnNhd_spectralProduct s c a w n l σ hw)

/-- Actual analytic nonvanishing of the full conjugate product: the
hypotheses concern parameters and counts, not algebraic nonvanishing. -/
theorem exists_conjugateProduct_ne_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c a w : ι → ℝ) (n k l : ι → ℕ) (signs : Finset (ι → Bool))
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hinj : Set.InjOn (fun i => (a i / w i)^2) {i | i ∈ s ∧ a i ≠ 0})
    (hk : ∀ i ∈ s, k i ≤ n i) (hl : ∀ i ∈ s, l i ≤ n i)
    (hdiff : ∃ g ∈ s, a g ≠ 0 ∧ k g ≠ l g) :
    ∃ x ∈ Ioo (0 : ℝ) 1, conjugateProduct s c a w n k l signs x ≠ 0 := by
  apply exists_finset_prod_ne_zero signs
  · intro σ _
    exact (analyticOnNhd_spectralProduct s c a w n k σ hw).sub
      (analyticOnNhd_spectralProduct s c a w n l σ hw)
  · intro σ _
    exact exists_spectralProduct_sub_ne_zero s c a w n k l σ hc hca hw hw1 hinj hk hl hdiff

/-- Finite-type specialization for all `2^b` sign choices when `ι = Fin b`. -/
theorem exists_all_conjugates_product_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c a w : ι → ℝ) (n k l : ι → ℕ)
    (hc : ∀ i, 0 < c i) (hca : ∀ i, c i^2-a i^2=1)
    (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i < 1)
    (hinj : Set.InjOn (fun i => (a i / w i)^2) {i | a i ≠ 0})
    (hk : ∀ i, k i ≤ n i) (hl : ∀ i, l i ≤ n i)
    (hdiff : ∃ g, a g ≠ 0 ∧ k g ≠ l g) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      (∏ σ : ι → Bool, (spectralProduct Finset.univ c a w n k σ x -
        spectralProduct Finset.univ c a w n l σ x)) ≠ 0 := by
  apply exists_conjugateProduct_ne_zero Finset.univ c a w n k l Finset.univ
    (fun i _ => hc i) (fun i _ => hca i) (fun i _ => hw i) (fun i _ => hw1 i)
  · intro i hi j hj hij
    exact hinj hi.2 hj.2 hij
  · exact fun i _ => hk i
  · exact fun i _ => hl i
  · obtain ⟨g, hag, hkl⟩ := hdiff
    exact ⟨g, Finset.mem_univ g, hag, hkl⟩

end PlanarHom.BooleanConjugateProducts
