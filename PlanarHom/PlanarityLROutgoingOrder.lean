import PlanarHom.PlanarityLRNesting

/-! NEW exact signed nesting order and the no-crossing-return consequence of
literal LR fork equations. These are the local facts used in contour assembly. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints

/-- The precise total order implemented by left reversal and right preservation. -/
def signedNestingLE (g : MixedCode) (bits : List Bool) (e f : ℕ) : Prop :=
  (edgeSide g bits e=false ∧ edgeSide g bits f=true) ∨
    (edgeSide g bits e=edgeSide g bits f ∧
      if edgeSide g bits e then nestingLE g e f=true else nestingLE g f e=true)

theorem signedNestingLE_antisymm (g : MixedCode) (bits : List Bool) (e f : ℕ)
    (hef : signedNestingLE g bits e f) (hfe : signedNestingLE g bits f e) : e=f := by
  cases he : edgeSide g bits e <;> cases hf : edgeSide g bits f <;>
    simp only [signedNestingLE,he,hf,Bool.false_eq_true,Bool.true_eq_false,false_and,and_false,
      false_or,true_and,or_false,reduceIte] at hef hfe
  · exact nestingLE_antisymm g f e hef hfe |>.symm
  · exact nestingLE_antisymm g e f hef hfe

theorem orderedOutgoing_signed_sorted (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (orderedOutgoing g bits v).Pairwise (signedNestingLE g bits) := by
  unfold orderedOutgoing
  rw [List.pairwise_append]
  have hn := nestingOutgoing_sorted g v
  refine ⟨?_,?_,?_⟩
  · rw [List.pairwise_reverse]
    apply (hn.filter (fun e => !(edgeSide g bits e))).imp_of_mem
    intro e f he hf hef
    have he' : edgeSide g bits e=false := by have h := (List.mem_filter.mp he).2; cases h' : edgeSide g bits e <;> simp_all
    have hf' : edgeSide g bits f=false := by have h := (List.mem_filter.mp hf).2; cases h' : edgeSide g bits f <;> simp_all
    exact Or.inr ⟨hf'.trans he'.symm,by simp only [hf',Bool.false_eq_true,reduceIte]; exact hef⟩
  · apply (hn.filter (edgeSide g bits)).imp_of_mem
    intro e f he hf hef
    have he' := (List.mem_filter.mp he).2
    have hf' := (List.mem_filter.mp hf).2
    exact Or.inr ⟨he'.trans hf'.symm,by simp only [he',reduceIte]; exact hef⟩
  · intro e he f hf
    have he' : edgeSide g bits e=false := by
      have h := (List.mem_filter.mp (List.mem_reverse.mp he)).2
      cases h' : edgeSide g bits e <;> simp_all
    exact Or.inl ⟨he',(List.mem_filter.mp hf).2⟩

theorem nestingLE_of_lowpoint_lt (g : MixedCode) {e f : ℕ} (h : lowpoint g e < lowpoint g f) :
    nestingLE g e f=true := by
  simp only [nestingLE,decide_eq_true_eq,nestingDepth]
  left
  split_ifs <;> omega

/-- Same-side branches cannot both have a return above the other's lowpoint.
This is a direct semantic consequence of the computed fork constraints. -/
theorem same_side_return_separation (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f b c : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hs : edgeSide g bits e=edgeSide g bits f)
    (hb : b ∈ returns g e) (hc : c ∈ returns g f) :
    targetHeight g b ≤ lowpoint g f ∨ targetHeight g c ≤ lowpoint g e := by
  by_cases hbf : targetHeight g b ≤ lowpoint g f
  · exact Or.inl hbf
  · by_cases hce : targetHeight g c ≤ lowpoint g e
    · exact Or.inr hce
    · have hbg : b ∈ (forkBlock g e f).1 := List.mem_filter.mpr ⟨hb,decide_eq_true (lt_of_not_ge hbf)⟩
      have hcg : c ∈ (forkBlock g f e).1 := List.mem_filter.mpr ⟨hc,decide_eq_true (lt_of_not_ge hce)⟩
      have hbs := edgeSide_of_fork_return g bits hLR hv hh he hf hne hbg
      have hcs := edgeSide_of_fork_return g bits hLR hv hh hf he hne.symm hcg
      have hneq := (hLR v hv hh e he f hf hne).2.2 b hbg c hcg
      exact False.elim (hneq (hbs.symm.trans (hs.trans hcs)))

 theorem orderedOutgoing_rank_lt_iff (g : MixedCode) (bits : List Bool) {v e f : ℕ}
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : e≠f) :
    (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f ↔
      signedNestingLE g bits e f := by
  let xs := orderedOutgoing g bits v
  have hem : e ∈ xs := (mem_orderedOutgoing g bits v e).mpr he
  have hfm : f ∈ xs := (mem_orderedOutgoing g bits v f).mpr hf
  have hei : xs.idxOf e < xs.length := List.idxOf_lt_length_iff.mpr hem
  have hfi : xs.idxOf f < xs.length := List.idxOf_lt_length_iff.mpr hfm
  have heg : xs[xs.idxOf e] = e := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun b => b == e) (w := hei))
  have hfg : xs[xs.idxOf f] = f := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun b => b == f) (w := hfi))
  have hsorted := List.pairwise_iff_getElem.mp (orderedOutgoing_signed_sorted g bits v)
  constructor
  · intro hlt
    have hrel := hsorted (xs.idxOf e) (xs.idxOf f) hei hfi hlt
    change signedNestingLE g bits xs[xs.idxOf e] xs[xs.idxOf f] at hrel
    simpa only [heg,hfg] using hrel
  · intro hrel
    rcases lt_trichotomy (xs.idxOf e) (xs.idxOf f) with hlt | heq | hlt
    · exact hlt
    · exact False.elim (hne (heg.symm.trans (by simpa only [heq] using hfg)))
    · have hrev := hsorted (xs.idxOf f) (xs.idxOf e) hfi hei hlt
      change signedNestingLE g bits xs[xs.idxOf f] xs[xs.idxOf e] at hrev
      have hrev' : signedNestingLE g bits f e := by simpa only [heg,hfg] using hrev
      exact False.elim (hne (signedNestingLE_antisymm g bits e f hrel hrev'))

 theorem chordal_false_returns_minimum (g : MixedCode) {e b : ℕ}
    (he : chordal g e=false) (hb : b ∈ returns g e) : targetHeight g b=lowpoint g e := by
  have hlo := lowpoint_le_return g e hb
  have hno : ¬lowpoint g e < targetHeight g b := by
    intro h
    have ht : chordal g e=true := List.any_eq_true.mpr ⟨b,hb,decide_eq_true h⟩
    rw [he] at ht
    contradiction
  omega

 theorem edgeSide_nonchordal (g : MixedCode) (bits : List Bool)
    (halign : PlanarityLRConstraintBlocks.Aligned (bitSide bits) (alignmentPairs g))
    {v e b : ℕ} (he : e ∈ outgoing g v) (hflat : chordal g e=false)
    (hb : b ∈ returns g e) : edgeSide g bits e=bitSide bits b := by
  obtain ⟨c,hc,hside,_⟩ := edgeSide_witness g bits e (fun h => by simpa [h] using hb)
  rw [hside]
  rcases (outgoing_spec g he).2.1 with ht | ht
  · apply halign (c,b)
    exact (mem_alignmentPairs g c b).mpr ⟨e,ht,hc,hb,
      chordal_false_returns_minimum g hflat hc,chordal_false_returns_minimum g hflat hb⟩
  · have htree := (of_decide_eq_true ht).2.1
    have hc' : c=e := by simpa only [returns,htree,Bool.false_eq_true,if_false,ht,if_true,List.mem_singleton] using hc
    have hb' : b=e := by simpa only [returns,htree,Bool.false_eq_true,if_false,ht,if_true,List.mem_singleton] using hb
    rw [hc',hb']

 theorem returns_at_root_nil (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v e : ℕ} (he : e ∈ outgoing g v) (hv : height g v=0) : returns g e=[] := by
  have hs := outgoing_spec g he
  rcases hs.2.1 with ht | ht
  · simp [returns,ht,hs.2.2,hv]
  · have hlt := back_height_lt g hg ht
    rw [hs.2.2,hv] at hlt
    omega

 theorem edgeSide_at_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (he : e ∈ outgoing g v) (hv : height g v=0) : edgeSide g bits e=true := by
  simp [edgeSide,returns_at_root_nil g hg he hv,maximumReturn]

 theorem outgoing_return_height_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v e b : ℕ} (he : e ∈ outgoing g v) (hb : b ∈ returns g e) : targetHeight g b < height g v := by
  have hs := outgoing_spec g he
  rcases hs.2.1 with ht | ht
  · simpa only [hs.2.2] using ((returns_tree_iff g ht b).mp hb).2.2
  · have htree := (of_decide_eq_true ht).2.1
    have hb' : b=e := by simpa only [returns,htree,Bool.false_eq_true,if_false,ht,if_true,List.mem_singleton] using hb
    rw [hb',← hs.2.2]
    exact back_height_lt g hg ht

/-- On one side, the lower-lowpoint branch cannot extend above the next branch's
lowpoint. This is the ordered interval separation needed for nested routing. -/
theorem same_side_lower_return_bound (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) {v e f b : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hs : edgeSide g bits e=edgeSide g bits f)
    (hl : lowpoint g e < lowpoint g f) (hb : b ∈ returns g e) :
    targetHeight g b ≤ lowpoint g f := by
  by_cases hnil : returns g f=[]
  · have hlp : lowpoint g f=height g v := by simp only [lowpoint,hnil,List.map_nil,List.foldl_nil,(outgoing_spec g hf).2.2]
    rw [hlp]
    exact (outgoing_return_height_lt g hg he hb).le
  · obtain ⟨c,hc⟩ := List.exists_mem_of_ne_nil (returns g f) hnil
    have hcl := lowpoint_le_return g f hc
    exact (same_side_return_separation g bits hLR hv hh he hf hne hs hb hc).resolve_right (by omega)

/-- Two chordal branches with the same lowpoint must be put on opposite sides. -/
theorem same_lowpoint_chordal_sides_ne (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e f : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he : e ∈ outgoing g v) (hf : f ∈ outgoing g v) (hne : f≠e)
    (hl : lowpoint g e=lowpoint g f) (hce : chordal g e=true) (hcf : chordal g f=true) :
    edgeSide g bits e≠edgeSide g bits f := by
  obtain ⟨b,hb,hbh⟩ := List.any_eq_true.mp hce
  obtain ⟨c,hc,hch⟩ := List.any_eq_true.mp hcf
  have hb' : lowpoint g e < targetHeight g b := of_decide_eq_true hbh
  have hc' : lowpoint g f < targetHeight g c := of_decide_eq_true hch
  intro hs
  have hsep := same_side_return_separation g bits hLR hv hh he hf hne hs hb hc
  omega

end PlanarHom.PlanarityLRDirect
