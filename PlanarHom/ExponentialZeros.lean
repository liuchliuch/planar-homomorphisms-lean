import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card

/-!
# Zeros of real exponential sums

This file proves Lemma 3.9: a nonzero linear combination of `n` distinct
positive real bases raised to a real variable has at most `n - 1` distinct
real zeros. The analytic proof is by induction, normalization by a positive
exponential, and Rolle's theorem. No integrality or algebraicity assumptions
on the bases or coefficients are needed.
-/

open scoped BigOperators

namespace PlanarHom

/-- A finite real exponential sum, with arbitrary real exponents. -/
noncomputable def exponentialSum {n : ℕ} (a c : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * Real.exp (a i * x)

/-- The derivative of a finite exponential sum is obtained term by term. -/
theorem hasDerivAt_exponentialSum {n : ℕ} (a c : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (exponentialSum a c)
      (exponentialSum a (fun i => c i * a i) x) x := by
  unfold exponentialSum
  simpa only [id_eq, mul_one, mul_assoc, mul_left_comm, mul_comm] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (((hasDerivAt_id x).const_mul (a i)).exp).const_mul (c i))

/-- Subtracting a common exponent multiplies the sum by a positive factor. -/
theorem exponentialSum_sub_exponent {n : ℕ} (a c : Fin n → ℝ) (b x : ℝ) :
    exponentialSum (fun i => a i - b) c x =
      exponentialSum a c x * Real.exp (-b * x) := by
  unfold exponentialSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (a i - b) * x = a i * x + -b * x by ring, Real.exp_add]
  ring

/-- Rolle's theorem produces an ordered family of derivative zeros between
an ordered family of zeros of the original function. -/
theorem exists_ordered_derivative_zeros {n : ℕ} {f f' : ℝ → ℝ}
    {x : Fin (n + 1) → ℝ} (hx : StrictMono x)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hz : ∀ i, f (x i) = 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧ ∀ i, f' (y i) = 0 := by
  have hbetween (i : Fin n) :
      ∃ y ∈ Set.Ioo (x i.castSucc) (x i.succ), f' y = 0 := by
    apply exists_hasDerivAt_eq_zero (hx (Fin.castSucc_lt_succ i))
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
    · rw [hz, hz]
    · exact fun t _ => hf t
  choose y hy hyz using hbetween
  refine ⟨y, ?_, hyz⟩
  intro i j hij
  have hij' : i.succ ≤ j.castSucc := by
    simpa only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
      using (show i.val + 1 ≤ j.val from hij)
  exact (hy i).2.trans_le (hx.monotone hij') |>.trans (hy j).1

/-- At `n` distinct ordered real sample points, a sum of `n` distinct real
exponentials can vanish only when all its coefficients vanish. -/
theorem exponentialSum_coefficients_eq_zero {n : ℕ} (a c x : Fin n → ℝ)
    (ha : Function.Injective a) (hx : StrictMono x)
    (hz : ∀ i, exponentialSum a c (x i) = 0) : ∀ i, c i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    let b : ℝ := a (Fin.last n)
    let a' : Fin n → ℝ := fun i => a i.castSucc - b
    let c' : Fin n → ℝ := fun i => c i.castSucc * (a i.castSucc - b)
    let g : ℝ → ℝ := exponentialSum (fun i => a i - b) c
    have hg (t : ℝ) : HasDerivAt g (exponentialSum a' c' t) t := by
      convert hasDerivAt_exponentialSum (fun i => a i - b) c t using 1
      simp [exponentialSum, Fin.sum_univ_castSucc, a', c', b]
    have hgz (i : Fin (n + 1)) : g (x i) = 0 := by
      dsimp [g]
      rw [exponentialSum_sub_exponent, hz, zero_mul]
    obtain ⟨y, hy, hyz⟩ := exists_ordered_derivative_zeros hx hg hgz
    have ha' : Function.Injective a' := by
      intro i j hij
      apply Fin.castSucc_injective
      apply ha
      exact sub_left_injective hij
    have hc' : ∀ i, c' i = 0 := ih a' c' y ha' hy hyz
    have hc (i : Fin n) : c i.castSucc = 0 := by
      have hne : a i.castSucc - b ≠ 0 := by
        intro heq
        have : i.castSucc = Fin.last n := ha (sub_eq_zero.mp heq)
        exact Fin.castSucc_ne_last i this
      exact (mul_eq_zero.mp (hc' i)).resolve_right hne
    have hlast : c (Fin.last n) = 0 := by
      have h := hz (Fin.last n)
      simp only [exponentialSum, Fin.sum_univ_castSucc] at h
      simp only [hc, zero_mul, Finset.sum_const_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right (Real.exp_ne_zero _)
    intro i
    exact Fin.lastCases hlast hc i

/-- Every finite set of zeros has fewer elements than the number of terms. -/
theorem exponentialSum_zero_finset_card_lt {n : ℕ} (a c : Fin n → ℝ)
    (ha : Function.Injective a) (hc : ∃ i, c i ≠ 0)
    (s : Finset ℝ) (hs : ∀ t ∈ s, exponentialSum a c t = 0) : s.card < n := by
  classical
  by_contra! h
  let x := s.orderEmbOfCardLe h
  have hzero := exponentialSum_coefficients_eq_zero a c x ha x.strictMono
    (fun i => hs _ (s.orderEmbOfCardLe_mem h i))
  obtain ⟨i, hi⟩ := hc
  exact hi (hzero i)

/-- A nontrivial sum of distinct real exponentials has a finite zero set. -/
theorem exponentialSum_zero_set_finite {n : ℕ} (a c : Fin n → ℝ)
    (ha : Function.Injective a) (hc : ∃ i, c i ≠ 0) :
    {t : ℝ | exponentialSum a c t = 0}.Finite := by
  classical
  by_contra h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h n
  have hlt := exponentialSum_zero_finset_card_lt a c ha hc s (fun t ht => hs ht)
  omega

/-- A nontrivial sum of `n` distinct real exponentials has at most `n - 1`
distinct real zeros. The extended cardinality formulation also rules out
an infinite zero set. -/
theorem exponentialSum_zero_set_encard_le {n : ℕ} (a c : Fin n → ℝ)
    (ha : Function.Injective a) (hc : ∃ i, c i ≠ 0) :
    {t : ℝ | exponentialSum a c t = 0}.encard ≤ (n - 1 : ℕ) := by
  classical
  have hfinite := exponentialSum_zero_set_finite a c ha hc
  apply Set.encard_le_coe_iff_finite_ncard_le.mpr
  refine ⟨hfinite, ?_⟩
  have hlt := exponentialSum_zero_finset_card_lt a c ha hc hfinite.toFinset
    (fun t ht => hfinite.mem_toFinset.mp ht)
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  omega

/-- The positive-base real-power expression used in the paper is exactly
an exponential sum with exponents given by logarithms of the bases. -/
theorem sum_rpow_eq_exponentialSum {n : ℕ} (μ c : Fin n → ℝ)
    (hμpos : ∀ i, 0 < μ i) (t : ℝ) :
    (∑ i, c i * (μ i) ^ t) = exponentialSum (fun i => Real.log (μ i)) c t := by
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (hμpos i)]

/-- `n` ordered real samples determine the coefficients of a linear
combination of `n` distinct positive bases raised to the sample parameter. -/
theorem rpowSum_coefficients_eq_zero {n : ℕ} (μ c x : Fin n → ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμ : Function.Injective μ) (hx : StrictMono x)
    (hz : ∀ j, (∑ i, c i * (μ i) ^ (x j)) = 0) : ∀ i, c i = 0 := by
  apply exponentialSum_coefficients_eq_zero (fun i => Real.log (μ i)) c x
  · intro i j h
    exact hμ (Real.log_injOn_pos (hμpos i) (hμpos j) h)
  · exact hx
  · simpa only [sum_rpow_eq_exponentialSum μ c hμpos] using hz

/-- The positive-base version of the zero bound, requiring only that the
bases be distinct, without prescribing an ordering. -/
theorem rpowSum_zero_set_encard_le {n : ℕ} (μ c : Fin n → ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμ : Function.Injective μ)
    (hc : ∃ i, c i ≠ 0) :
    {t : ℝ | (∑ i, c i * (μ i) ^ t) = 0}.encard ≤ (n - 1 : ℕ) := by
  have hlog : Function.Injective (fun i => Real.log (μ i)) := by
    intro i j h
    exact hμ (Real.log_injOn_pos (hμpos i) (hμpos j) h)
  simpa only [sum_rpow_eq_exponentialSum μ c hμpos] using
    exponentialSum_zero_set_encard_le (fun i => Real.log (μ i)) c hlog hc

/-- **Lemma 3.9 (Zeros of exponential sums).** For strictly increasing
positive real bases and coefficients not all zero, the real-power sum has
at most `n - 1` distinct real zeros. -/
theorem lemma_3_9 {n : ℕ} (μ c : Fin n → ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμ : StrictMono μ) (hc : c ≠ 0) :
    {t : ℝ | (∑ i, c i * (μ i) ^ t) = 0}.encard ≤ (n - 1 : ℕ) := by
  apply rpowSum_zero_set_encard_le μ c hμpos hμ.injective
  by_contra! h
  exact hc (funext h)

end PlanarHom
