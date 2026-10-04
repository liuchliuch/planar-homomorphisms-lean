import PlanarHom.ProductCompatibility
import PlanarHom.FixedAlgebraicField
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.Field.Basic

/-! Exact product-map hypotheses for the support, magnitude and sign transforms
in Corollary 3.2. Actual joint-reduction wrappers are separate. -/
noncomputable section
namespace PlanarHom.ProductCompatibility
variable {I : Type}

theorem compatible_monoidHom {K : Type} [Field K] (A : I → K) (f : K →* K) :
    Compatible A (fun i => f (A i)) := by
  intro xs ys _ _ _ heq
  simpa only [map_list_prod, List.map_map, Function.comp_def] using congrArg f heq

def supportTransform (A : I → ℝ) (i : I) : ℝ := if A i = 0 then 0 else 1

theorem compatible_support (A : I → ℝ) : Compatible A (supportTransform A) := by
  intro xs ys _ hx hy _
  have hp (zs : List I) (hz : ∀ i ∈ zs, A i ≠ 0) : (zs.map (supportTransform A)).prod = 1 := by
    apply List.prod_eq_one
    intro x hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    simp [supportTransform, hz i hi]
  rw [hp xs hx, hp ys hy]

theorem compatible_abs (A : I → ℝ) : Compatible A (fun i => |A i|) :=
  compatible_monoidHom A (absHom : ℝ →*₀ ℝ).toMonoidHom

private def signHom : ℝ →* ℝ where
  toFun x := x / |x|
  map_one' := by norm_num
  map_mul' x y := by
    simp only [abs_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

private theorem signHom_eq (x : ℝ) : signHom x = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · change x / |x| = _
    rw [abs_of_neg hx, Real.sign_of_neg hx]
    simp [div_neg, div_self (ne_of_lt hx)]
  · simp [signHom]
  · change x / |x| = _
    rw [abs_of_pos hx, Real.sign_of_pos hx, div_self (ne_of_gt hx)]

theorem compatible_sign (A : I → ℝ) : Compatible A (fun i => Real.sign (A i)) := by
  simpa only [signHom_eq] using compatible_monoidHom A signHom

theorem hasProductMaps_support (A : I → ℝ) : HasProductMaps A (supportTransform A) :=
  hasProductMaps_of_compatible _ _ (compatible_support A)

theorem hasProductMaps_abs (A : I → ℝ) : HasProductMaps A (fun i => |A i|) :=
  hasProductMaps_of_compatible _ _ (compatible_abs A)

theorem hasProductMaps_sign (A : I → ℝ) : HasProductMaps A (fun i => Real.sign (A i)) :=
  hasProductMaps_of_compatible _ _ (compatible_sign A)

private theorem prod_nonneg_real (xs : List ℝ) (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact mul_nonneg (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Exact equality case at a positive lower endpoint, including the empty word. -/
theorem prod_eq_lower_pow_iff (c : ℝ) (hc : 0 < c) (xs : List ℝ)
    (hx : ∀ x ∈ xs, c ≤ x) :
    c ^ xs.length ≤ xs.prod ∧ (xs.prod = c ^ xs.length ↔ ∀ x ∈ xs, x = c) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hcx := hx x (by simp)
    obtain ⟨hle, heq⟩ := ih (fun y hy => hx y (by simp [hy]))
    have hp : 0 < xs.prod := (pow_pos hc _).trans_le hle
    have hm := mul_eq_mul_iff_eq_and_eq_of_pos hcx hle hc hp
    constructor
    · simpa only [List.length_cons, List.prod_cons, pow_succ'] using
        mul_le_mul hcx hle (pow_nonneg hc.le _) (hc.le.trans hcx)
    · simp only [List.length_cons, List.prod_cons, pow_succ', List.forall_mem_cons]
      rw [eq_comm, hm]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, heq.mp h2.symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, (heq.mpr h2).symm⟩

/-- Exact equality case at a positive upper endpoint. -/
theorem prod_eq_upper_pow_iff (c : ℝ) (hc : 0 < c) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 < x ∧ x ≤ c) :
    xs.prod ≤ c ^ xs.length ∧ (xs.prod = c ^ xs.length ↔ ∀ x ∈ xs, x = c) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    obtain ⟨hle, heq⟩ := ih (fun y hy => hx y (by simp [hy]))
    have hm := mul_eq_mul_iff_eq_and_eq_of_pos hx0.2 hle hx0.1 (pow_pos hc _)
    constructor
    · simpa only [List.length_cons, List.prod_cons, pow_succ'] using
        mul_le_mul hx0.2 hle (prod_nonneg_real xs (fun y hy => (hx y (by simp [hy])).1.le)) hc.le
    · simp only [List.length_cons, List.prod_cons, pow_succ', List.forall_mem_cons]
      rw [hm, heq]

private theorem prod_indicator (P : I → Prop) [DecidablePred P] (xs : List I) :
    (xs.map (fun i => if P i then (1 : ℝ) else 0)).prod = if ∀ i ∈ xs, P i then 1 else 0 := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : P x <;> by_cases hs : ∀ i ∈ xs, P i <;> simp [hx, hs, ih]

def extremalMask (A : I → ℝ) (c : ℝ) (i : I) : ℝ := if A i = c then 1 else 0

theorem compatible_lower_mask (A : I → ℝ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ i, A i ≠ 0 → c ≤ A i) : Compatible A (extremalMask A c) := by
  classical
  intro xs ys hlen hxs hys heq
  have hword (zs : List I) (hz : ∀ i ∈ zs, A i ≠ 0) :
      (zs.map (extremalMask A c)).prod = if (zs.map A).prod = c ^ zs.length then 1 else 0 := by
    have hp := (prod_eq_lower_pow_iff c hc (zs.map A) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hbound i (hz i hi))).2
    simp only [List.length_map, List.forall_mem_map] at hp
    change (zs.map (fun i => if A i = c then (1 : ℝ) else 0)).prod = _
    rw [prod_indicator]
    simp only [hp]
  rw [hword xs hxs, hword ys hys, heq, hlen]

theorem compatible_upper_mask (A : I → ℝ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ i, A i ≠ 0 → 0 < A i ∧ A i ≤ c) : Compatible A (extremalMask A c) := by
  classical
  intro xs ys hlen hxs hys heq
  have hword (zs : List I) (hz : ∀ i ∈ zs, A i ≠ 0) :
      (zs.map (extremalMask A c)).prod = if (zs.map A).prod = c ^ zs.length then 1 else 0 := by
    have hp := (prod_eq_upper_pow_iff c hc (zs.map A) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hbound i (hz i hi))).2
    simp only [List.length_map, List.forall_mem_map] at hp
    change (zs.map (fun i => if A i = c then (1 : ℝ) else 0)).prod = _
    rw [prod_indicator]
    simp only [hp]
  rw [hword xs hxs, hword ys hys, heq, hlen]

theorem supportTransform_zero (A : I → ℝ) {i : I} (h : A i = 0) : supportTransform A i = 0 := by
  simp [supportTransform, h]

theorem extremalMask_zero (A : I → ℝ) {c : ℝ} (hc : 0 < c) {i : I} (h : A i = 0) :
    extremalMask A c i = 0 := by
  simp [extremalMask, h, ne_of_lt hc]

theorem supportTransform_isAlgebraic (A : I → ℝ) (i : I) : IsAlgebraic ℚ (supportTransform A i) := by
  unfold supportTransform
  split
  · exact isAlgebraic_zero
  · exact isAlgebraic_one

theorem abs_isAlgebraic {x : ℝ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ |x| := by
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using h
  · simpa only [abs_of_nonpos hx] using h.neg

theorem sign_isAlgebraic (x : ℝ) : IsAlgebraic ℚ (Real.sign x) := by
  rcases Real.sign_apply_eq x with h | h | h
  · rw [h]
    exact (isAlgebraic_one (R := ℚ) (A := ℝ)).neg
  · rw [h]
    exact isAlgebraic_zero
  · rw [h]
    exact isAlgebraic_one

theorem extremalMask_isAlgebraic (A : I → ℝ) (c : ℝ) (i : I) : IsAlgebraic ℚ (extremalMask A c i) := by
  unfold extremalMask
  split
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

/-- This literal entry identity is the reverse mixed-language parallel factorization. -/
theorem abs_mul_real_sign (x : ℝ) : |x| * Real.sign x = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    simp
  · simp
  · rw [abs_of_pos hx, Real.sign_of_pos hx, mul_one]

/-- Actual attained positive endpoints of the nonzero magnitudes. The maximum
also bounds every zero entry, and no signed-entry ordering is substituted. -/
theorem exists_extremal_magnitudes [Fintype I] (A : I → ℝ) (hnz : ∃ i, A i ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∃ i, |A i| = a) ∧ (∃ i, |A i| = b) ∧
      (∀ i, A i ≠ 0 → a ≤ |A i|) ∧ (∀ i, |A i| ≤ b) := by
  classical
  let s := (Finset.univ.image (fun i => |A i|)).erase 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hnz
    exact ⟨|A i|, Finset.mem_erase.mpr ⟨abs_ne_zero.mpr hi, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩
  let a := s.min' hs
  let b := s.max' hs
  have ha : a ∈ s := Finset.min'_mem s hs
  have hb : b ∈ s := Finset.max'_mem s hs
  obtain ⟨ia, _, hia⟩ := Finset.mem_image.mp (Finset.mem_erase.mp ha).2
  obtain ⟨ib, _, hib⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hb).2
  have hap : 0 < a := lt_of_le_of_ne (hia ▸ abs_nonneg (A ia)) (Ne.symm (Finset.mem_erase.mp ha).1)
  have hbp : 0 < b := lt_of_le_of_ne (hib ▸ abs_nonneg (A ib)) (Ne.symm (Finset.mem_erase.mp hb).1)
  refine ⟨a, b, hap, hbp, ⟨ia, hia⟩, ⟨ib, hib⟩, ?_, ?_⟩
  · intro i hi
    exact Finset.min'_le s |A i| (Finset.mem_erase.mpr ⟨abs_ne_zero.mpr hi,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  · intro i
    by_cases hi : A i = 0
    · simpa only [hi, abs_zero] using hbp.le
    · exact Finset.le_max' s |A i| (Finset.mem_erase.mpr ⟨abs_ne_zero.mpr hi,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

end PlanarHom.ProductCompatibility
