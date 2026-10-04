import PlanarHom.PlanarityLRRealizationArches

/-! NEW explicit reversed-slot routing across one omitted parent-fan interval.
Inputs are scanned above the interval then below it; slots decrease inside it. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization

/-- Circular increasing order after deleting one closed real fan interval. -/
def AfterGapOrder (L U x y : ℝ) : Prop :=
  (U<x ∧ x<y) ∨ (x<y ∧ y<L) ∨ (U<x ∧ y<L)

 theorem Noninterleaving.symm {a b c d : ℝ} (h : Noninterleaving a b c d) : Noninterleaving c d a b := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Reversed slots give genuinely separated/nested matching intervals, including
pairs that straddle the chart cut at the omitted pole. -/
theorem reversed_slots_noninterleaving {L U x y s t : ℝ}
    (hslots : L<t ∧ t<s ∧ s<U) (horder : AfterGapOrder L U x y) :
    Noninterleaving (min x s) (max x s) (min y t) (max y t) := by
  rcases horder with ⟨hUx,hxy⟩ | ⟨hxy,hyL⟩ | ⟨hUx,hyL⟩
  · have hsx : s<x := hslots.2.2.trans hUx
    have hty : t<y := hslots.2.1.trans (hsx.trans hxy)
    rw [min_eq_right hsx.le,max_eq_left hsx.le,min_eq_right hty.le,max_eq_left hty.le]
    exact Or.inr (Or.inr (Or.inr ⟨hslots.2.1,hxy⟩))
  · have hyt : y<t := hyL.trans hslots.1
    have hxs : x<s := hxy.trans (hyt.trans hslots.2.1)
    rw [min_eq_left hxs.le,max_eq_right hxs.le,min_eq_left hyt.le,max_eq_right hyt.le]
    exact Or.inr (Or.inr (Or.inl ⟨hxy,hslots.2.1⟩))
  · have hsx : s<x := hslots.2.2.trans hUx
    have hyt : y<t := hyL.trans hslots.1
    rw [min_eq_right hsx.le,max_eq_left hsx.le,min_eq_left hyt.le,max_eq_right hyt.le]
    exact Or.inr (Or.inl hslots.2.1)

/-- Concrete finite lane slots, strictly inside the parent interval. -/
def reversedSlot (L U : ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  L+(U-L)*(((n:ℝ)-(i.val:ℝ))/((n:ℝ)+1))

 theorem reversedSlot_bounds {L U : ℝ} (hLU : L<U) (n : ℕ) (i : Fin n) :
    L<reversedSlot L U n i ∧ reversedSlot L U n i<U := by
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hi : 0≤(i.val:ℝ) := Nat.cast_nonneg _
  have hni : (i.val:ℝ)<(n:ℝ) := Nat.cast_lt.mpr i.isLt
  have hd : 0<(n:ℝ)+1 := by linarith
  have hq : 0<((n:ℝ)-(i.val:ℝ))/((n:ℝ)+1) := div_pos (sub_pos.mpr hni) hd
  have hq1 : ((n:ℝ)-(i.val:ℝ))/((n:ℝ)+1)<1 := (div_lt_one hd).mpr (by linarith)
  have hw : 0<U-L := sub_pos.mpr hLU
  have hp := mul_pos hw hq
  have hp1 := mul_lt_mul_of_pos_left hq1 hw
  simp only [reversedSlot]
  constructor <;> nlinarith

 theorem reversedSlot_strictAnti {L U : ℝ} (hLU : L<U) (n : ℕ) : StrictAnti (reversedSlot L U n) := by
  intro i j hij
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hd : 0<(n:ℝ)+1 := by linarith
  have hij' : (i.val:ℝ)<(j.val:ℝ) := Nat.cast_lt.mpr hij
  have hq : ((n:ℝ)-(j.val:ℝ))/((n:ℝ)+1)<((n:ℝ)-(i.val:ℝ))/((n:ℝ)+1) :=
    div_lt_div_of_pos_right (by linarith) hd
  have hp := mul_lt_mul_of_pos_left hq (sub_pos.mpr hLU)
  simp only [reversedSlot]
  linarith

 theorem reversed_slot_family_noninterleaving {L U : ℝ} (hLU : L<U) (n : ℕ) (input : Fin n → ℝ)
    (horder : ∀ i j, i<j → AfterGapOrder L U (input i) (input j))
    (i j : Fin n) (hne : i≠j) :
    Noninterleaving (min (input i) (reversedSlot L U n i)) (max (input i) (reversedSlot L U n i))
      (min (input j) (reversedSlot L U n j)) (max (input j) (reversedSlot L U n j)) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact reversed_slots_noninterleaving
      ⟨(reversedSlot_bounds hLU n j).1,reversedSlot_strictAnti hLU n hij,(reversedSlot_bounds hLU n i).2⟩
      (horder i j hij)
  · exact (reversed_slots_noninterleaving
      ⟨(reversedSlot_bounds hLU n i).1,reversedSlot_strictAnti hLU n hji,(reversedSlot_bounds hLU n j).2⟩
      (horder j i hji)).symm

 theorem outside_ne_reversedSlot {L U x : ℝ} (hLU : L<U) (n : ℕ) (i : Fin n)
    (hx : x<L ∨ U<x) : x≠reversedSlot L U n i := by
  have hs := reversedSlot_bounds hLU n i
  rcases hx with hx | hx <;> intro heq <;> rw [heq] at hx <;> linarith

/-- Pairwise disjoint literal full arch ranges for the constructed lane slots. -/
theorem reversed_slot_arches_disjoint {L U : ℝ} (hLU : L<U) (n : ℕ) (input : Fin n → ℝ)
    (hout : ∀ i, input i<L ∨ U<input i)
    (horder : ∀ i j, i<j → AfterGapOrder L U (input i) (input j)) (x : ℝ)
    (i j : Fin n) (hne : i≠j) :
    Disjoint (Set.range (arch x (input i) (reversedSlot L U n i)))
      (Set.range (arch x (input j) (reversedSlot L U n j))) :=
  arch_ranges_disjoint_unordered x _ _ _ _
    (outside_ne_reversedSlot hLU n i (hout i)) (outside_ne_reversedSlot hLU n j (hout j))
    (reversed_slot_family_noninterleaving hLU n input horder i j hne)

end PlanarHom.PlanarityLRRealization
