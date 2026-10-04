import PlanarHom.CommonWeightedAmplitudeCoordinates
import Mathlib.Tactic.NormNum

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom.CommonWeightedAmplitudeCoordinates

namespace WeightedChartRegression

/-- The support uniqueness lemma handles no nodes. -/
theorem empty_support (a b node : Fin 0 → ℝ) : a = b := by
  apply finite_type_moment_unique (node := node)
  · intro i
    exact Fin.elim0 i
  · intro m
    simp

/-- The fiber-equivalence lemma also handles an empty ambient type: its two
fibers are both empty. Surjectivity is deliberately not needed by this lemma. -/
theorem empty_fibers (classOf : Fin 0 → Bool) (a w : Fin 0 → ℝ) :
    ∃ e : {x // classOf x = false} ≃ {x // classOf x = true},
      (∀ x, a (e x).val = a x.val) ∧ (∀ x, w (e x).val = w x.val) := by
  apply exists_weighted_fiber_equiv classOf a w
  · intro x
    exact Fin.elim0 x
  · intro x
    exact Fin.elim0 x
  · intro s x
    exact Fin.elim0 x.val
  · intro s t m
    have hs : IsEmpty {x // classOf x = s} := ⟨fun x => Fin.elim0 x.val⟩
    have ht : IsEmpty {x // classOf x = t} := ⟨fun x => Fin.elim0 x.val⟩
    simp

/-- A nonempty class type prevents the forbidden empty-ambient case of the
positive-size chart theorem. -/
theorem no_empty_surjection {S : Type*} [Nonempty S] (classOf : Fin 0 → S) :
    ¬ Function.Surjective classOf := by
  intro h
  obtain ⟨x, hx⟩ := h (Classical.arbitrary S)
  exact Fin.elim0 x

/-- There is intentionally no `[Fintype S]` assumption in this API test. -/
theorem exact_consumer_interface {X S : Type*} [Fintype X] [Nonempty S]
    (classOf : X → S) (hsurj : Function.Surjective classOf)
    (a w : X → ℝ) (ha : ∀ x, 0 < a x) (hw : ∀ x, 0 < w x)
    (hinj : ∀ s, Function.Injective (fun x : {x // classOf x = s} => a x.val))
    (hmom : ∀ s t, ∀ m : ℕ,
      (∑ x : {x // classOf x = s}, w x.val * a x.val ^ (2*m)) =
        ∑ y : {y // classOf y = t}, w y.val * a y.val ^ (2*m)) :
    ∃ k, ∃ amplitudes masses : Fin k → ℝ, ∃ e : X ≃ S × Fin k,
      0 < k ∧ (∀ i, 0 < amplitudes i) ∧ (∀ i, 0 < masses i) ∧
      (∀ x, (e x).1 = classOf x) ∧
      (∀ x, a x = amplitudes (e x).2) ∧
      (∀ x, w x = masses (e x).2) := by
  obtain ⟨k, amplitudes, masses, e, hk, ha', hw', he, hax, hwx⟩ :=
    exists_common_weighted_chart classOf hsurj a w ha hw hinj hmom
  exact ⟨k, amplitudes, masses, e, hk, ha', hw', he, hax, hwx⟩

private def pairFiber (s : Bool) : {x : Bool × Bool // x.1 = s} ≃ Bool where
  toFun x := x.val.2
  invFun i := ⟨(s, i), rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.symm rfl
  right_inv i := rfl

private def amplitude (x : Bool × Bool) : ℝ := if x.2 then 2 else 1
private def weight (x : Bool × Bool) : ℝ := if x.2 then 7/3 else 3/2

private theorem amplitude_pos (x : Bool × Bool) : 0 < amplitude x := by
  cases h : x.2 <;> norm_num [amplitude, h]
private theorem weight_pos (x : Bool × Bool) : 0 < weight x := by
  cases h : x.2 <;> norm_num [weight, h]
private theorem amplitude_inj (s : Bool) :
    Function.Injective (fun x : {x : Bool × Bool // x.1 = s} => amplitude x.val) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext (x.property.trans y.property.symm)
  cases hx : x.val.2 <;> cases hy : y.val.2 <;> simp_all [amplitude]

private theorem moments_equal (s t : Bool) (m : ℕ) :
    (∑ x : {x : Bool × Bool // x.1 = s}, weight x.val * amplitude x.val ^ (2*m)) =
      ∑ y : {y : Bool × Bool // y.1 = t}, weight y.val * amplitude y.val ^ (2*m) := by
  let f : Bool → ℝ := fun i => (if i then 7/3 else 3/2) * (if i then 2 else 1) ^ (2*m)
  exact ((pairFiber s).sum_comp f).trans ((pairFiber t).sum_comp f).symm

/-- Two classes each contain two distinct amplitudes with unequal, nonintegral
positive weights. The result retains the actual weights, not multiplicities. -/
theorem unequal_nonintegral_weights :
    ∃ k, ∃ a mass : Fin k → ℝ, ∃ e : (Bool × Bool) ≃ Bool × Fin k,
      0 < k ∧ (∀ i, 0 < a i) ∧ (∀ i, 0 < mass i) ∧
      (∀ x, (e x).1 = x.1) ∧
      (∀ x, amplitude x = a (e x).2) ∧
      (∀ x, weight x = mass (e x).2) := by
  exact exists_common_weighted_chart Prod.fst (fun s => ⟨(s, false), rfl⟩)
    amplitude weight amplitude_pos weight_pos amplitude_inj (by
      intro s t m
      convert moments_equal s t m using 1 <;>
        apply Finset.sum_congr (by ext x; simp) <;> intro x hx <;> rfl)

/-- This regression explicitly checks that the two recovered weights differ. -/
theorem distinct_recovered_weights :
    ∃ k, ∃ mass : Fin k → ℝ, ∃ i j : Fin k,
      mass i = 3/2 ∧ mass j = 7/3 ∧ mass i ≠ mass j := by
  obtain ⟨k, a, mass, e, hk, ha, hw, he, hea, hew⟩ := unequal_nonintegral_weights
  refine ⟨k, mass, (e (false, false)).2, (e (false, true)).2, ?_, ?_, ?_⟩
  · simpa [weight] using (hew (false, false)).symm
  · simpa [weight] using (hew (false, true)).symm
  · rw [← hew (false, false), ← hew (false, true)]
    norm_num [weight]

end WeightedChartRegression
