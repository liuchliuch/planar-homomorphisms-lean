import PlanarHom.IntervalBisectionMachines
import Mathlib.Order.Monotone.Basic

/-! # Sign partitions of monotone functions on integer intervals

Intervals are half open. Two binary lower-bound searches split an increasing
function into its negative, zero, and positive portions. Empty portions are
kept, so one split always returns at most three intervals.
-/

namespace PlanarHom.DiscreteSignPartition

abbrev Interval := ℕ × ℕ

def threshold (test : ℕ → Bool) (l h : ℕ) : ℕ :=
  l + IntervalBisection.cut (fun _ : Unit => fun t => test (l+t)) () (h-l-1)

theorem threshold_spec (test : ℕ → Bool) (l h : ℕ) (hlh : l < h)
    (hm : ∀ a b, l ≤ a → a ≤ b → b < h → test a = true → test b = true) :
    l ≤ threshold test l h ∧ threshold test l h ≤ h ∧
      ∀ t, l ≤ t → t < h → (test t = true ↔ threshold test l h ≤ t) := by
  have hs := IntervalBisection.cut_spec
    (fun _ : Unit => fun t => test (l+t)) () (h-l-1) (by
      intro a b hab hb ha
      exact hm (l+a) (l+b) (by omega) (by omega) (by omega) ha)
  refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
  · unfold threshold
    omega
  · intro t ht ht'
    have he := hs.2 (t-l) (by omega)
    dsimp only at he
    rw [Nat.add_sub_of_le ht] at he
    unfold threshold
    constructor
    · intro hp
      have := he.mp hp
      omega
    · intro hp
      apply he.mpr
      omega

def SignConstant (f : ℕ → ℚ) (I : Interval) : Prop :=
  (∀ t, I.1 ≤ t → t < I.2 → f t < 0) ∨
  (∀ t, I.1 ≤ t → t < I.2 → f t = 0) ∨
  (∀ t, I.1 ≤ t → t < I.2 → 0 < f t)

def splitIncreasing (f : ℕ → ℚ) (l h : ℕ) : List Interval :=
  if l < h then
    let a := threshold (fun t => decide (0 ≤ f t)) l h
    let b := threshold (fun t => decide (0 < f t)) l h
    [(l,a), (a,b), (b,h)]
  else [(l,h)]

theorem increasing_thresholds (f : ℕ → ℚ) (l h : ℕ) (hlh : l < h)
    (hf : MonotoneOn f (Set.Ico l h)) :
    let a := threshold (fun t => decide (0 ≤ f t)) l h
    let b := threshold (fun t => decide (0 < f t)) l h
    l ≤ a ∧ a ≤ b ∧ b ≤ h ∧
      (∀ t, l ≤ t → t < h → (0 ≤ f t ↔ a ≤ t)) ∧
      (∀ t, l ≤ t → t < h → (0 < f t ↔ b ≤ t)) := by
  have hge := threshold_spec (fun t => decide (0 ≤ f t)) l h hlh (by
    intro a b ha hab hb ht
    simp only [decide_eq_true_eq] at ht ⊢
    exact ht.trans (hf ⟨ha, by omega⟩ ⟨by omega, hb⟩ hab))
  have hgt := threshold_spec (fun t => decide (0 < f t)) l h hlh (by
    intro a b ha hab hb ht
    simp only [decide_eq_true_eq] at ht ⊢
    exact ht.trans_le (hf ⟨ha, by omega⟩ ⟨by omega, hb⟩ hab))
  simp only [decide_eq_true_eq] at hge hgt
  dsimp only
  refine ⟨hge.1, ?_, hgt.2.1, hge.2.2, hgt.2.2⟩
  by_cases hb : threshold (fun t => decide (0 < f t)) l h < h
  · have hp := (hgt.2.2 _ hgt.1 hb).mpr le_rfl
    exact (hge.2.2 _ hgt.1 hb).mp hp.le
  · omega

theorem splitIncreasing_bounds (f : ℕ → ℚ) (l h : ℕ) (hlh : l ≤ h)
    (hf : MonotoneOn f (Set.Ico l h)) (I : Interval) (hI : I ∈ splitIncreasing f l h) :
    l ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ h := by
  unfold splitIncreasing at hI
  split_ifs at hI with hh
  · obtain ⟨ha, hab, hb, _, _⟩ := increasing_thresholds f l h hh hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl <;> dsimp only at * <;> omega
  · have he := List.mem_singleton.mp hI
    subst I
    exact ⟨le_rfl, hlh, le_rfl⟩

theorem splitIncreasing_cover (f : ℕ → ℚ) (l h : ℕ) (hlh : l ≤ h)
    (hf : MonotoneOn f (Set.Ico l h)) (t : ℕ) (ht : l ≤ t) (ht' : t < h) :
    ∃ I ∈ splitIncreasing f l h, I.1 ≤ t ∧ t < I.2 := by
  have hh : l < h := lt_of_le_of_lt ht ht'
  obtain ⟨ha, hab, hb, _, _⟩ := increasing_thresholds f l h hh hf
  unfold splitIncreasing
  rw [if_pos hh]
  dsimp only
  by_cases h₁ : t < threshold (fun t => decide (0 ≤ f t)) l h
  · exact ⟨(l, threshold (fun t => decide (0 ≤ f t)) l h), by simp, ht, h₁⟩
  · by_cases h₂ : t < threshold (fun t => decide (0 < f t)) l h
    · exact ⟨(threshold (fun t => decide (0 ≤ f t)) l h,
        threshold (fun t => decide (0 < f t)) l h), by simp, by dsimp only; omega, h₂⟩
    · exact ⟨(threshold (fun t => decide (0 < f t)) l h, h),
        by simp, by dsimp only; omega, ht'⟩

theorem splitIncreasing_sign (f : ℕ → ℚ) (l h : ℕ) (hlh : l ≤ h)
    (hf : MonotoneOn f (Set.Ico l h)) (I : Interval) (hI : I ∈ splitIncreasing f l h) :
    SignConstant f I := by
  unfold splitIncreasing at hI
  split_ifs at hI with hh
  · obtain ⟨ha, hab, hb, hge, hgt⟩ := increasing_thresholds f l h hh hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl
    · left
      intro t ht ht'
      have hh' : t < h := by omega
      have hn : ¬ 0 ≤ f t := by intro hp; have := (hge t ht hh').mp hp; omega
      exact lt_of_not_ge hn
    · right; left
      intro t ht ht'
      have htl : l ≤ t := by omega
      have hth : t < h := by omega
      have h₁ : 0 ≤ f t := (hge t htl hth).mpr ht
      have h₂ : ¬ 0 < f t := by intro hp; have := (hgt t htl hth).mp hp; omega
      exact le_antisymm (le_of_not_gt h₂) h₁
    · right; right
      intro t ht ht'
      exact (hgt t (by omega) ht').mpr ht
  · have he := List.mem_singleton.mp hI
    subst I
    left
    intro t ht ht'
    omega

theorem splitIncreasing_length (f : ℕ → ℚ) (l h : ℕ) :
    (splitIncreasing f l h).length ≤ 3 := by
  unfold splitIncreasing
  split <;> simp

end PlanarHom.DiscreteSignPartition
