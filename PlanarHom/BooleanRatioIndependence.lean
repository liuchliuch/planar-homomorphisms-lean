import PlanarHom.BooleanRatioParity
import PlanarHom.BooleanParameterSeparation

/-!
# The genuine integer-power ratio identity in Section 5.1

The ratio functions use the positive real square root and integer exponents.
The proof eliminates equal-diagonal classes by analytic parity, differentiates
the remaining logarithmic identity, and applies the proved real branch-point
independence theorem. No sign-flip or monodromy assumption is present.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace PlanarHom.BooleanRatioIndependence
open BooleanEigenvalueBranches BooleanSquareRootIndependence BooleanRatioParity

/-- Factoring out the positive weight gives precisely the branch parameter
used in the analytic kernel theorem. -/
theorem root_eq_scaled_sqrt (a w y : ℝ) (hw : 0 < w) :
    root a w y = w * Real.sqrt (y + (a/w)^2) := by
  have heq : a^2+w^2*y = w^2*(y+(a/w)^2) := by
    field_simp
    ring
  rw [root, heq, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw.le]

/-- An identity of signed integer powers of the actual positive eigenvalue
ratios forces every unequal-diagonal exponent to vanish. Equal-diagonal
classes are deliberately absent from the conclusion. -/
theorem ratio_product_identity_exponents_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c a w : ι → ℝ) (z : ι → ℤ)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hinj : Set.InjOn (fun i => (a i / w i)^2) {i | i ∈ s ∧ a i ≠ 0})
    (hid : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∏ i ∈ s, ratio (c i) (a i) (w i) (x^2) ^ z i = 1) :
    ∀ i ∈ s, a i ≠ 0 → z i = 0 := by
  classical
  let S := s.filter (fun i => a i ≠ 0)
  let b := fun i => (a i/w i)^2
  let v := fun i => w i^2
  let q := fun i => -(z i : ℝ)*c i*w i
  have hlog := unequal_log_identity s c a w z hc hca hw hw1 hid
  have hS (i : ι) (hi : i ∈ S) : i ∈ s ∧ a i ≠ 0 := Finset.mem_filter.mp hi
  have hb (i : ι) (hi : i ∈ S) : 0 < b i :=
    sq_pos_of_ne_zero (div_ne_zero (hS i hi).2 (ne_of_gt (hw i (hS i hi).1)))
  have hv1 (i : ι) (hi : i ∈ S) : v i < 1 := by
    dsimp [v]
    have hp := hw i (hS i hi).1
    have hu := hw1 i (hS i hi).1
    nlinarith
  have hsum : ∀ y ∈ Ioo (0 : ℝ) 1, ∑ i ∈ S, q i * kernel (b i) (v i) y = 0 := by
    intro y hy
    have hr (i : ι) (hi : i ∈ S) : 0 < a i^2+w i^2*y := by
      have hapos := sq_pos_of_ne_zero (hS i hi).2
      have hn := mul_nonneg (sq_nonneg (w i)) hy.1.le
      linarith
    have hd (i : ι) (hi : i ∈ S) : w i^2*y < 1 := by
      have hv := hv1 i hi
      have h := mul_le_mul_of_nonneg_left hy.2.le (sq_nonneg (w i))
      dsimp [v] at hv
      nlinarith
    have hderiv := HasDerivAt.fun_sum (u := S) fun i hi =>
      (hasDerivAt_logRatio (c i) (a i) (w i) y (hc i (hS i hi).1)
        (hca i (hS i hi).1) (hr i hi) (hd i hi)).const_mul (z i : ℝ)
    have hevent : (fun t => ∑ i ∈ S, (z i : ℝ)*logRatio (c i) (a i) (w i) t) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
      exact hlog t ht
    have hconst := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hevent
    have hzero := hderiv.unique hconst
    rw [← hzero]
    apply Finset.sum_congr rfl
    intro i hi
    have hwne := ne_of_gt (hw i (hS i hi).1)
    have hsne : Real.sqrt (y+(a i/w i)^2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by have := hb i hi; dsimp [b] at this; linarith [hy.1]))
    have hdne : 1-w i^2*y ≠ 0 := ne_of_gt (sub_pos.mpr (hd i hi))
    rw [root_eq_scaled_sqrt _ _ _ (hw i (hS i hi).1)]
    dsimp [q, b, v, kernel]
    field_simp [hwne, hsne, hdne]
  have hind := kernel_linearIndependent S b v q hb
    (fun i hi j hj h => hinj (hS i hi) (hS j hj) h)
    (fun i _ => sq_nonneg (w i)) hv1 hsum
  intro i hi hai
  have hq := hind i (Finset.mem_filter.mpr ⟨hi, hai⟩)
  dsimp [q] at hq
  have hci := ne_of_gt (hc i hi)
  have hwi := ne_of_gt (hw i hi)
  have hz : (z i : ℝ) = 0 := by
    simpa [mul_eq_zero, hci, hwi] using hq
  exact_mod_cast hz

/-- The paper's genuine ratio as a function of the original variable `x`. -/
def delta (θ w : ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  ratio (cParameter θ t) (aParameter θ t) w (x^2)

/-- This definition is literally the positive-square-root formula (5.3). -/
theorem delta_eq_formula (θ w : ℝ) (t : ℕ) (x : ℝ) :
    delta θ w t x =
      (cParameter θ t - Real.sqrt ((aParameter θ t)^2+w^2*x^2)) /
      (cParameter θ t + Real.sqrt ((aParameter θ t)^2+w^2*x^2)) := rfl

theorem aParameter_div_eq_beta (θ w : ℝ) (t : ℕ) :
    aParameter θ t / w = BooleanParameterSeparation.beta θ w t :=
  (BooleanParameterSeparation.beta_eq_half_difference_div θ w t).symm

/-- The exact implication following equation (5.4): distinct positive branch
parameters force the exponent of every unequal-diagonal class to vanish.
The premise is an identity of genuine real functions on the oracle interval,
not an assumed algebraic-function or monodromy relation. -/
theorem source_ratio_identity {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (θ w : ι → ℝ) (t : ℕ) (z : ι → ℤ)
    (ht : 0 < t) (hθ : ∀ i ∈ G, 1 ≤ θ i)
    (hw : ∀ i ∈ G, 0 < w i) (hw1 : ∀ i ∈ G, w i < 1)
    (hβ : Set.InjOn (fun i => BooleanParameterSeparation.beta (θ i) (w i) t)
      {i | i ∈ G ∧ 1 < θ i})
    (hid : ∀ x ∈ Ioo (0 : ℝ) 1, ∏ i ∈ G, delta (θ i) (w i) t x ^ z i = 1) :
    ∀ i ∈ G, 1 < θ i → z i = 0 := by
  have hθpos (i : ι) (hi : i ∈ G) : 0 < θ i := lt_of_lt_of_le zero_lt_one (hθ i hi)
  have hsqinj : Set.InjOn (fun i => (aParameter (θ i) t / w i)^2)
      {i | i ∈ G ∧ aParameter (θ i) t ≠ 0} := by
    intro i hi j hj heq
    have hθi := (aParameter_ne_zero_iff (hθ i hi.1) ht).mp hi.2
    have hθj := (aParameter_ne_zero_iff (hθ j hj.1) ht).mp hj.2
    apply hβ ⟨hi.1, hθi⟩ ⟨hj.1, hθj⟩
    dsimp only at heq ⊢
    rw [aParameter_div_eq_beta, aParameter_div_eq_beta] at heq
    have hbi := BooleanParameterSeparation.beta_pos hθi (hw i hi.1) ht
    have hbj := BooleanParameterSeparation.beta_pos hθj (hw j hj.1) ht
    nlinarith
  have hresult := ratio_product_identity_exponents_zero G
    (fun i => cParameter (θ i) t) (fun i => aParameter (θ i) t) w z
    (fun i hi => cParameter_pos (hθpos i hi) t)
    (fun i hi => parameter_identity (θ i) t (ne_of_gt (hθpos i hi)))
    hw hw1 hsqinj hid
  intro i hi hgt
  exact hresult i hi (ne_of_gt (aParameter_pos hgt ht))

/-- For a finite family of genuine parameter-class representatives there is
a common positive odd exponent at which the source ratio implication holds
for every signed integer exponent vector. -/
theorem exists_positive_odd_source_ratio_independence {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (θ w : ι → ℝ)
    (hθ : ∀ i ∈ G, 1 ≤ θ i) (hw : ∀ i ∈ G, 0 < w i)
    (hw1 : ∀ i ∈ G, w i < 1)
    (hrep : Set.InjOn (fun i => (θ i, w i)) (↑G : Set ι)) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧ ∀ z : ι → ℤ,
      (∀ x ∈ Ioo (0 : ℝ) 1, ∏ i ∈ G, delta (θ i) (w i) t x ^ z i = 1) →
      ∀ i ∈ G, 1 < θ i → z i = 0 := by
  obtain ⟨t, ht, ho, _, hinj⟩ :=
    BooleanParameterSeparation.exists_positive_odd_representatives G θ w hw hrep
  exact ⟨t, ht, ho, fun z hid => source_ratio_identity G θ w t z ht hθ hw hw1 hinj hid⟩

end PlanarHom.BooleanRatioIndependence
