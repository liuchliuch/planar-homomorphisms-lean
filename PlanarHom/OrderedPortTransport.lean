import PlanarHom.OrderedPortIntervals
import Mathlib.Data.List.Nodup

/-! NEW transport of strict port separation/nesting along a verified key order. -/
namespace PlanarHom

 theorem PortNoncrossing.map_with {A K H : Type*} [LinearOrder K] [LinearOrder H]
    (key : A → K) (height : A → H)
    (hmono : ∀ {a b}, key a < key b → height a < height b)
    {a b c d : A} (h : PortNoncrossing (key a) (key b) (key c) (key d)) :
    PortNoncrossing (height a) (height b) (height c) (height d) := by
  have separated (a b c d : A) (hs : max (key a) (key b) < min (key c) (key d)) :
      PortNoncrossing (height a) (height b) (height c) (height d) := by
    apply portNoncrossing_separated
    · exact hmono ((le_max_left _ _).trans_lt (hs.trans_le (min_le_left _ _)))
    · exact hmono ((le_max_left _ _).trans_lt (hs.trans_le (min_le_right _ _)))
    · exact hmono ((le_max_right _ _).trans_lt (hs.trans_le (min_le_left _ _)))
    · exact hmono ((le_max_right _ _).trans_lt (hs.trans_le (min_le_right _ _)))
  rcases h with h | h | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact separated a b c d h
  · exact (separated c d a b h).symm
  · rcases le_total (key a) (key b) with hab | hba
    · rw [min_eq_left hab] at h₁
      rw [max_eq_right hab] at h₂
      exact (portNoncrossing_inside (hmono (h₁.trans_le (min_le_left _ _)))
        (hmono (h₁.trans_le (min_le_right _ _)))
        (hmono ((le_max_left _ _).trans_lt h₂))
        (hmono ((le_max_right _ _).trans_lt h₂))).symm
    · rw [min_eq_right hba] at h₁
      rw [max_eq_left hba] at h₂
      exact (portNoncrossing_inside (hmono (h₁.trans_le (min_le_left _ _)))
        (hmono (h₁.trans_le (min_le_right _ _)))
        (hmono ((le_max_left _ _).trans_lt h₂))
        (hmono ((le_max_right _ _).trans_lt h₂))).symm.swap_left
  · rcases le_total (key c) (key d) with hcd | hdc
    · rw [min_eq_left hcd] at h₁
      rw [max_eq_right hcd] at h₂
      exact portNoncrossing_inside (hmono (h₁.trans_le (min_le_left _ _)))
        (hmono (h₁.trans_le (min_le_right _ _)))
        (hmono ((le_max_left _ _).trans_lt h₂))
        (hmono ((le_max_right _ _).trans_lt h₂))
    · rw [min_eq_right hdc] at h₁
      rw [max_eq_left hdc] at h₂
      exact (portNoncrossing_inside (hmono (h₁.trans_le (min_le_left _ _)))
        (hmono (h₁.trans_le (min_le_right _ _)))
        (hmono ((le_max_left _ _).trans_lt h₂))
        (hmono ((le_max_right _ _).trans_lt h₂))).swap_right

 theorem sorted_key_idxOf_lt {A K : Type*} [BEq A] [LawfulBEq A] [LinearOrder K]
    (xs : List A) (key : A → K) (hs : xs.Pairwise (fun a b => key a < key b))
    {a b : A} (ha : a ∈ xs) (hb : b ∈ xs) (hkey : key a < key b) : xs.idxOf a < xs.idxOf b := by
  have hi : xs.idxOf a < xs.length := List.idxOf_lt_length_iff.mpr ha
  have hj : xs.idxOf b < xs.length := List.idxOf_lt_length_iff.mpr hb
  have hga : xs[xs.idxOf a]=a := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun c => c == a) (w := hi))
  have hgb : xs[xs.idxOf b]=b := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun c => c == b) (w := hj))
  by_contra hno
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hno) with hlt | heq
  · have hrev := List.pairwise_iff_getElem.mp hs (xs.idxOf b) (xs.idxOf a) hj hi hlt
    rw [hgb,hga] at hrev
    exact lt_asymm hkey hrev
  · have hab : a=b := hga.symm.trans (by simpa only [heq] using hgb)
    rw [hab] at hkey
    exact lt_irrefl _ hkey

 theorem idxOf_mem_injective {A : Type*} [BEq A] [LawfulBEq A] (xs : List A) :
    Function.Injective (fun a : {a : A // a ∈ xs} => xs.idxOf a.val) := by
  intro a b heq
  apply Subtype.ext
  have hi : xs.idxOf a.val < xs.length := List.idxOf_lt_length_iff.mpr a.property
  have hj : xs.idxOf b.val < xs.length := List.idxOf_lt_length_iff.mpr b.property
  have hga : xs[xs.idxOf a.val]=a.val := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun c => c == a.val) (w := hi))
  have hgb : xs[xs.idxOf b.val]=b.val := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun c => c == b.val) (w := hj))
  exact hga.symm.trans (by simpa only [heq] using hgb)

end PlanarHom
