import PlanarHom.PlanarityLRForkOrderSemantics
import PlanarHom.PlanarityLRBackEdgeForks

/-! NEW full aligned fork order: a right return cannot precede a left return
from another outgoing branch. The lowpoint and alignment facts are all derived. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints
open PlanarityLRConstraintBlocks

 theorem mixed_returns_minimum (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hord : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f)
    (hbs : bitSide bits b=true) (hcs : bitSide bits c=false) :
    targetHeight g b=targetHeight g c ∧ lowpoint g e=targetHeight g b ∧
      lowpoint g f=targetHeight g b ∧ ∀ d ∈ outgoing g v, targetHeight g b≤lowpoint g d := by
  have hbc := le_antisymm (right_return_le_of_before g bits hLR hv hh he hf hne hord hb hc hbs)
    (left_return_le_of_after g bits hLR hv hh he hf hne hord hb hc hcs)
  have hloE := lowpoint_le_return g e hb
  have hloF := lowpoint_le_return g f hc
  have horder := (orderedOutgoing_rank_lt_iff g bits he hf hne.symm).mp hord
  have hemin : lowpoint g e=targetHeight g b := by
    by_contra hno
    have hlt : lowpoint g e < targetHeight g c := by omega
    have hcg : c ∈ (forkBlock g f e).1 := List.mem_filter.mpr ⟨hc,decide_eq_true hlt⟩
    have hfL := (edgeSide_of_fork_return g bits hLR hv hh hf he hne.symm hcg).trans hcs
    have heo := signedNestingLE_of_left g bits horder hfL
    have hle := nestingLE_lowpoint_le g heo.2
    have hbg : b ∈ (forkBlock g e f).1 := List.mem_filter.mpr ⟨hb,decide_eq_true (by omega)⟩
    have heR := (edgeSide_of_fork_return g bits hLR hv hh he hf hne hbg).trans hbs
    rw [heR] at heo
    simp at heo
  have hfmin : lowpoint g f=targetHeight g b := by
    by_contra hno
    have hlt : lowpoint g f < targetHeight g b := by omega
    have hbg : b ∈ (forkBlock g e f).1 := List.mem_filter.mpr ⟨hb,decide_eq_true hlt⟩
    have heR := (edgeSide_of_fork_return g bits hLR hv hh he hf hne hbg).trans hbs
    have hfo := signedNestingLE_of_right g bits horder heR
    have hle := nestingLE_lowpoint_le g hfo.2
    have hcg : c ∈ (forkBlock g f e).1 := List.mem_filter.mpr ⟨hc,decide_eq_true (by omega)⟩
    have hfL := (edgeSide_of_fork_return g bits hLR hv hh hf he hne.symm hcg).trans hcs
    rw [hfL] at hfo
    simp at hfo
  refine ⟨hbc,hemin,hfmin,?_⟩
  intro d hd
  by_contra hno
  have hlt : lowpoint g d < targetHeight g b := lt_of_not_ge hno
  have hde : d≠e := by intro h; rw [h,hemin] at hlt; omega
  have hdf : d≠f := by intro h; rw [h,hfmin] at hlt; omega
  have hbg : b ∈ (forkBlock g e d).1 := List.mem_filter.mpr ⟨hb,decide_eq_true hlt⟩
  have hcg : c ∈ (forkBlock g f d).1 := List.mem_filter.mpr ⟨hc,decide_eq_true (by omega)⟩
  have heR := (edgeSide_of_fork_return g bits hLR hv hh he hd hde hbg).trans hbs
  have hfL := (edgeSide_of_fork_return g bits hLR hv hh hf hd hdf hcg).trans hcs
  have hfo := (signedNestingLE_of_right g bits horder heR).1
  rw [hfL] at hfo
  contradiction

/-- Actual aligned LR constraints prohibit right-before-left return events at
any outgoing fork of the computed row. -/
theorem no_right_before_left_returns (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits))
    (halign : Aligned (bitSide bits) (alignmentPairs g)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hord : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f)
    (hbs : bitSide bits b=true) (hcs : bitSide bits c=false) : False := by
  obtain ⟨hbc,hemin,hfmin,hall⟩ := mixed_returns_minimum g bits hLR hv hh he hf hne hord hb hc hbs hcs
  have hbh := outgoing_return_height_lt g hg he hb
  have hparent := parent_height g hv hh
  have hple : targetHeight g b≤height g (parentVertex g v) := by omega
  by_cases hlt : targetHeight g b < height g (parentVertex g v)
  · let p := parentEdge g v
    have hp := parentEdge_tree g hg hv hh
    have hbdesc := returns_source_descendant g hg e hb
    have hcdesc := returns_source_descendant g hg f hc
    rw [(outgoing_spec g he).2.2] at hbdesc
    rw [(outgoing_spec g hf).2.2] at hcdesc
    have hbP : b ∈ returns g p := (returns_tree_iff g hp.1 b).mpr
      ⟨mem_returns_back g e hb,by simpa only [hp.2.1] using hbdesc,by simpa only [hp.2.2] using hlt⟩
    have hcP : c ∈ returns g p := (returns_tree_iff g hp.1 c).mpr
      ⟨mem_returns_back g f hc,by simpa only [hp.2.1] using hcdesc,by simpa only [hp.2.2,← hbc] using hlt⟩
    have hlower : targetHeight g b≤lowpoint g p := by
      apply (le_lowpoint_iff g p _).mpr
      refine ⟨?_,?_⟩
      · change targetHeight g b≤height g (source g (parentEdge g v))
        rw [hp.2.2]
        exact hple
      · intro d hd
        have hD := (returns_tree_iff g hp.1 d).mp hd
        have hvd : Desc g v (source g d) := by simpa only [hp.2.1] using hD.2.1
        obtain ⟨j,hj⟩ := exists_back_branch g hg hD.1 hvd
        have hdheight : targetHeight g d < height g v := by
          have hh' := hD.2.2
          rw [hp.2.2] at hh'
          omega
        exact (hall j hj.outgoing).trans (lowpoint_le_return g j (hj.return_mem hD.1 hdheight))
    have hpmin : lowpoint g p=targetHeight g b := le_antisymm (lowpoint_le_return g p hbP) hlower
    have hal := halign (b,c) ((mem_alignmentPairs g b c).mpr
      ⟨p,hp.1,hbP,hcP,hpmin.symm,hbc.symm.trans hpmin.symm⟩)
    rw [hbs,hcs] at hal
    contradiction
  · have ht : targetHeight g b=height g (parentVertex g v) := by omega
    have hflat (j : ℕ) (hj : j ∈ outgoing g v) (hmin : lowpoint g j=targetHeight g b) : chordal g j=false := by
      apply Bool.eq_false_iff.mpr
      intro hcj
      obtain ⟨d,hd,hhigher⟩ := List.any_eq_true.mp hcj
      have hhigher' : lowpoint g j < targetHeight g d := of_decide_eq_true hhigher
      have hsmall := outgoing_return_height_lt g hg hj hd
      omega
    have heR := (edgeSide_nonchordal g bits halign he (hflat e he hemin) hb).trans hbs
    have hfL := (edgeSide_nonchordal g bits halign hf (hflat f hf hfmin) hc).trans hcs
    have horder := (orderedOutgoing_rank_lt_iff g bits he hf hne.symm).mp hord
    have hfR := (signedNestingLE_of_right g bits horder heR).1
    rw [hfL] at hfR
    contradiction

/-- Specialization to the actual compiled raw-input LR assignment. -/
theorem computed_no_right_before_left_returns (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hord : (orderedOutgoing g (decideAligned g).2 v).idxOf e < (orderedOutgoing g (decideAligned g).2 v).idxOf f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f)
    (hbs : bitSide (decideAligned g).2 b=true) (hcs : bitSide (decideAligned g).2 c=false) : False := by
  have hs := decideAligned_sound g hflag
  exact no_right_before_left_returns g hg (decideAligned g).2 hs.1 hs.2 hv hh he hf hne hord hb hc hbs hcs

end PlanarHom.PlanarityLRDirect
