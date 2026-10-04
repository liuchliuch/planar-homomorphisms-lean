import PlanarHom.PlanarityLROutgoingOrder

/-! NEW fork-order semantics for the literal LR row algorithm. On a common side,
nesting rank orders every return height; constrained returns determine that side. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints

theorem nestingLE_lowpoint_le (g : MixedCode) {e f : ℕ} (h : nestingLE g e f=true) :
    lowpoint g e≤lowpoint g f := by
  simp only [nestingLE,decide_eq_true_eq,nestingDepth] at h
  split_ifs at h <;> omega

theorem nestingLE_chordal_of_equal_lowpoint (g : MixedCode) {e f : ℕ}
    (h : nestingLE g e f=true) (hl : lowpoint g e=lowpoint g f) (he : chordal g e=true) : chordal g f=true := by
  simp only [nestingLE,decide_eq_true_eq,nestingDepth,he,hl,reduceIte] at h
  cases hf : chordal g f with
  | false => simp only [hf,Bool.false_eq_true,reduceIte] at h; omega
  | true => rfl

theorem same_side_nesting_returns_monotone (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hs : edgeSide g bits e=edgeSide g bits f) (hnest : nestingLE g e f=true)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f) : targetHeight g b≤targetHeight g c := by
  by_contra hno
  have hbc : targetHeight g c < targetHeight g b := lt_of_not_ge hno
  have hlf := lowpoint_le_return g f hc
  have hle := nestingLE_lowpoint_le g hnest
  have hsep := same_side_return_separation g bits hLR hv hh he hf hne hs hb hc
  have hce : targetHeight g c≤lowpoint g e := hsep.resolve_left (by omega)
  have heq : lowpoint g e=lowpoint g f := by omega
  have hec : chordal g e=true := List.any_eq_true.mpr ⟨b,hb,decide_eq_true (by omega)⟩
  have hfc := nestingLE_chordal_of_equal_lowpoint g hnest heq hec
  exact same_lowpoint_chordal_sides_ne g bits hLR hv hh he hf hne heq hec hfc hs

 theorem signedNestingLE_of_right (g : MixedCode) (bits : List Bool) {e f : ℕ}
    (h : signedNestingLE g bits e f) (he : edgeSide g bits e=true) :
    edgeSide g bits f=true ∧ nestingLE g e f=true := by
  rcases h with ⟨he',_⟩ | ⟨hs,hn⟩
  · rw [he] at he'; contradiction
  · exact ⟨hs.symm.trans he,by simpa only [he,reduceIte] using hn⟩

 theorem signedNestingLE_of_left (g : MixedCode) (bits : List Bool) {e f : ℕ}
    (h : signedNestingLE g bits e f) (hf : edgeSide g bits f=false) :
    edgeSide g bits e=false ∧ nestingLE g f e=true := by
  rcases h with ⟨_,hf'⟩ | ⟨hs,hn⟩
  · rw [hf] at hf'; contradiction
  · have he := hs.trans hf
    exact ⟨he,by simpa only [he,Bool.false_eq_true,reduceIte] using hn⟩

/-- A right return in an earlier branch cannot end above a later branch's return. -/
theorem right_return_le_of_before (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hord : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f) (hbs : bitSide bits b=true) :
    targetHeight g b≤targetHeight g c := by
  by_contra hno
  have hbc := lt_of_not_ge hno
  have hcut : lowpoint g f < targetHeight g b := (lowpoint_le_return g f hc).trans_lt hbc
  have hbg : b ∈ (forkBlock g e f).1 := List.mem_filter.mpr ⟨hb,decide_eq_true hcut⟩
  have heR : edgeSide g bits e=true := (edgeSide_of_fork_return g bits hLR hv hh he hf hne hbg).trans hbs
  have horder := (orderedOutgoing_rank_lt_iff g bits he hf hne.symm).mp hord
  have hfo := signedNestingLE_of_right g bits horder heR
  exact hno (same_side_nesting_returns_monotone g bits hLR hv hh he hf hne (heR.trans hfo.1.symm) hfo.2 hb hc)

/-- A left return in a later branch cannot end above an earlier branch's return. -/
theorem left_return_le_of_after (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hord : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f) (hcs : bitSide bits c=false) :
    targetHeight g c≤targetHeight g b := by
  by_contra hno
  have hbc := lt_of_not_ge hno
  have hcut : lowpoint g e < targetHeight g c := (lowpoint_le_return g e hb).trans_lt hbc
  have hcg : c ∈ (forkBlock g f e).1 := List.mem_filter.mpr ⟨hc,decide_eq_true hcut⟩
  have hfL : edgeSide g bits f=false := (edgeSide_of_fork_return g bits hLR hv hh hf he hne.symm hcg).trans hcs
  have horder := (orderedOutgoing_rank_lt_iff g bits he hf hne.symm).mp hord
  have heo := signedNestingLE_of_left g bits horder hfL
  exact hno (same_side_nesting_returns_monotone g bits hLR hv hh hf he hne.symm (hfL.trans heo.1.symm) heo.2 hc hb)

end PlanarHom.PlanarityLRDirect
