import PlanarHom.PlanarityLRAlignment
import PlanarHom.PlanarityLRReturnFacts

/-! NEW safe alignment for the actual DFS return-edge blocks. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PlanarityDepthFirstSearch PlanarityLRConstraintBlocks PlanarityParitySolver

def Desc (g : MixedCode) (u v : ℕ) : Prop := u = v ∨ u ∈ ancestors g v

theorem desc_trans (g : MixedCode) {u v w : ℕ} (hw : w < g.vertices)
    (huv : Desc g u v) (hvw : Desc g v w) : Desc g u w := by
  rcases huv with rfl | huv
  · exact hvw
  rcases hvw with rfl | hvw
  · exact Or.inr huv
  · exact Or.inr (ancestors_trans g hw huv hvw)

theorem desc_height_le (g : MixedCode) {u v : ℕ} (hv : v < g.vertices) (h : Desc g u v) :
    height g u ≤ height g v := by
  rcases h with rfl | h
  · exact le_rfl
  · exact (ancestors_height_lt g hv h).le

theorem desc_valid (g : MixedCode) {u v : ℕ} (hv : v < g.vertices) (h : Desc g u v) : u < g.vertices := by
  rcases h with rfl | h
  · exact hv
  · exact ancestors_valid g hv h

theorem desc_comparable (g : MixedCode) {u v w : ℕ} (hw : w < g.vertices)
    (hu : Desc g u w) (hv : Desc g v w) : Desc g u v ∨ Desc g v u := by
  rcases hu with rfl | hu
  · exact Or.inr hv
  rcases hv with rfl | hv
  · exact Or.inl (Or.inr hu)
  rcases ancestors_comparable g hw hu hv with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

theorem desc_of_height_le (g : MixedCode) {u v w : ℕ} (hw : w < g.vertices)
    (hu : Desc g u w) (hv : Desc g v w) (hle : height g u ≤ height g v) : Desc g u v := by
  rcases desc_comparable g hw hu hv with h | h
  · exact h
  · rcases h with h | h
    · exact Or.inl h.symm
    · have hh := ancestors_height_lt g (desc_valid g hw hu) h
      omega

theorem returns_tree_iff (g : MixedCode) {e : ℕ} (he : isTree g e = true) (b : ℕ) :
    b ∈ returns g e ↔ isBack g b = true ∧ Desc g (target g e) (source g b) ∧
      targetHeight g b < height g (source g e) := by
  simp only [returns,he,if_true,List.mem_filter,List.mem_range,Bool.and_eq_true,
    ancestor,decide_eq_true_eq,Desc]
  constructor
  · rintro ⟨_,⟨hb,ha⟩,hh⟩
    exact ⟨hb,ha,hh⟩
  · rintro ⟨hb,ha,hh⟩
    exact ⟨(of_decide_eq_true hb).1,⟨hb,ha⟩,hh⟩

theorem outgoing_spec (g : MixedCode) {v e : ℕ} (h : e ∈ outgoing g v) :
    e < g.edges.length ∧ (isTree g e = true ∨ isBack g e = true) ∧ source g e = v := by
  have hh := List.mem_filter.mp h
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hh
  exact ⟨List.mem_range.mp hh.1,hh.2.1,hh.2.2⟩

/-- Lowpoints cannot decrease inside the descendant subtree of a tree edge. -/
theorem lowpoint_descendant_mono (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e f : ℕ} (he : isTree g e = true) (hf : f < g.edges.length)
    (hdesc : Desc g (target g e) (source g f)) : lowpoint g e ≤ lowpoint g f := by
  have hsf := (source_target_valid g hg hf).1
  have hheight := desc_height_le g hsf hdesc
  have hstep := tree_height_succ g hg he
  have hlow := lowpoint_le_source g e
  apply (le_lowpoint_iff g f _).mpr
  refine ⟨by omega,?_⟩
  intro b hb
  by_cases hlt : targetHeight g b < height g (source g e)
  · have hsb := (source_target_valid g hg (returns_valid g f hb)).1
    have hdesc' := desc_trans g hsb hdesc (returns_source_descendant g hg f hb)
    exact lowpoint_le_return g e ((returns_tree_iff g he b).mpr
      ⟨mem_returns_back g f hb,hdesc',hlt⟩)
  · omega

/-- If a minimal return edge is constrained at a fork, all returns attaining the
same lowpoint in that subtree occur on the same side of that exact fork. -/
theorem aligned_returns_same_fork_side (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e b c v f₁ f₂ : ℕ} (he : isTree g e = true)
    (hb : b ∈ returns g e) (hc : c ∈ returns g e)
    (hbmin : targetHeight g b = lowpoint g e) (hcmin : targetHeight g c = lowpoint g e)
    (hf₁ : f₁ ∈ outgoing g v) (hf₂ : f₂ ∈ outgoing g v)
    (hbside : b ∈ (forkBlock g f₁ f₂).1) : c ∈ (forkBlock g f₁ f₂).1 := by
  have hf1 := outgoing_spec g hf₁
  have hf2 := outgoing_spec g hf₂
  have hbm := List.mem_filter.mp hbside
  have hcut : lowpoint g f₂ < targetHeight g b := of_decide_eq_true hbm.2
  have hbR := (returns_tree_iff g he b).mp hb
  have hcR := (returns_tree_iff g he c).mp hc
  have hsb := (source_target_valid g hg (returns_valid g e hb)).1
  have hsc := (source_target_valid g hg (returns_valid g e hc)).1
  have hv : v < g.vertices := hf1.2.2 ▸ (source_target_valid g hg hf1.1).1
  have hno : ¬Desc g (target g e) v := by
    intro h
    have hh := lowpoint_descendant_mono g hg he hf2.1 (hf2.2.2.symm ▸ h)
    omega
  have hvsb : Desc g v (source g b) := by
    simpa only [hf1.2.2] using returns_source_descendant g hg f₁ hbm.1
  have hve : Desc g v (target g e) := (desc_comparable g hsb hvsb hbR.2.1).resolve_right hno
  have hve' : v ∈ ancestors g (target g e) := by
    rcases hve with h | h
    · exact (hno (Or.inl h.symm)).elim
    · exact h
  have htvalid := (source_target_valid g hg (of_decide_eq_true he).1).2
  have hveheight := ancestors_height_lt g htvalid hve'
  have hf1tree : isTree g f₁ = true := by
    rcases hf1.2.1 with ht | ht
    · exact ht
    · have hnt : isTree g f₁ = false := (of_decide_eq_true ht).2.1
      have hbeq : b = f₁ := by simpa only [returns,hnt,Bool.false_eq_true,if_false,ht,if_true,List.mem_singleton] using hbm.1
      have h := hbR.2.1
      rw [hbeq,hf1.2.2] at h
      exact (hno h).elim
  have hbF := (returns_tree_iff g hf1tree b).mp hbm.1
  have hfh := tree_height_succ g hg hf1tree
  have hdesctarget : Desc g (target g f₁) (target g e) :=
    desc_of_height_le g hsb hbF.2.1 hbR.2.1 (by rw [hf1.2.2] at hfh; omega)
  have hctarget := desc_trans g hsc hdesctarget hcR.2.1
  have hcF : c ∈ returns g f₁ := (returns_tree_iff g hf1tree c).mpr
    ⟨hcR.1,hctarget,by omega⟩
  exact List.mem_filter.mpr ⟨hcF,decide_eq_true (by omega)⟩



def minimumReturns (g : MixedCode) (e : ℕ) : List ℕ :=
  (returns g e).filter (fun b => decide (targetHeight g b = lowpoint g e))

/-- Literal pairwise alignment equalities for every computed tree edge. -/
def alignmentPairs (g : MixedCode) : List AlignmentPair :=
  ((List.range g.edges.length).filter (isTree g)).flatMap (fun e =>
    (minimumReturns g e).flatMap (fun b => (minimumReturns g e).map (fun c => (b,c))))

theorem mem_alignmentPairs (g : MixedCode) (b c : ℕ) : (b,c) ∈ alignmentPairs g ↔
    ∃ e, isTree g e = true ∧ b ∈ returns g e ∧ c ∈ returns g e ∧
      targetHeight g b = lowpoint g e ∧ targetHeight g c = lowpoint g e := by
  constructor
  · intro h
    obtain ⟨e,he,h⟩ := List.mem_flatMap.mp h
    obtain ⟨b',hb',h⟩ := List.mem_flatMap.mp h
    obtain ⟨c',hc',hp⟩ := List.mem_map.mp h
    cases hp
    have hb := List.mem_filter.mp hb'
    have hc := List.mem_filter.mp hc'
    exact ⟨e,(List.mem_filter.mp he).2,hb.1,hc.1,of_decide_eq_true hb.2,of_decide_eq_true hc.2⟩
  · rintro ⟨e,he,hb,hc,hbmin,hcmin⟩
    apply List.mem_flatMap.mpr
    refine ⟨e,List.mem_filter.mpr ⟨List.mem_range.mpr (of_decide_eq_true he).1,he⟩,?_⟩
    exact List.mem_flatMap.mpr ⟨b,List.mem_filter.mpr ⟨hb,decide_eq_true hbmin⟩,
      List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨hc,decide_eq_true hcmin⟩,rfl⟩⟩

private theorem alignment_witness (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e b c : ℕ} (he : isTree g e = true) (hb : b ∈ returns g e) (hc : c ∈ returns g e)
    (hbmin : targetHeight g b = lowpoint g e) (hcmin : targetHeight g c = lowpoint g e)
    (hocc : Occurs (forkBlocks g) b) :
    ∃ B ∈ forkBlocks g, (b ∈ B.1 ∧ c ∈ B.1) ∨ (b ∈ B.2 ∧ c ∈ B.2) := by
  obtain ⟨B,hB,hside⟩ := hocc
  obtain ⟨v,hv,hh,f₁,hf₁,f₂,hf₂,hne,rfl⟩ := (mem_forkBlocks g B).mp hB
  refine ⟨forkBlock g f₁ f₂,(mem_forkBlocks g _).mpr ⟨v,hv,hh,f₁,hf₁,f₂,hf₂,hne,rfl⟩,?_⟩
  rcases hside with hside | hside
  · exact Or.inl ⟨hside,aligned_returns_same_fork_side g hg he hb hc hbmin hcmin hf₁ hf₂ hside⟩
  · exact Or.inr ⟨hside,aligned_returns_same_fork_side g hg he hb hc hbmin hcmin hf₂ hf₁ hside⟩

/-- Alignment safety is derived from the actual raw-code DFS and lowpoints.
It is not supplied as a certificate or an additional graph promise. -/
theorem alignmentPairs_safe (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    AlignmentSafe (forkBlocks g) (alignmentPairs g) := by
  intro p hp hocc
  rcases p with ⟨b,c⟩
  obtain ⟨e,he,hb,hc,hbmin,hcmin⟩ := (mem_alignmentPairs g b c).mp hp
  rcases hocc with hocc | hocc
  · exact alignment_witness g hg he hb hc hbmin hcmin hocc
  · obtain ⟨B,hB,hside⟩ := alignment_witness g hg he hc hb hcmin hbmin hocc
    exact ⟨B,hB,hside.elim (fun h => Or.inl ⟨h.2,h.1⟩) (fun h => Or.inr ⟨h.2,h.1⟩)⟩

def solveAlignedLR (g : MixedCode) : Bool × Assignment :=
  decideAlignedBlocks (forkBlocks g,alignmentPairs g)

theorem solveAlignedLR_sound (g : MixedCode) (h : (solveAlignedLR g).1 = true) :
    LRCondition g (lookup (solveAlignedLR g).2) ∧ Aligned (lookup (solveAlignedLR g).2) (alignmentPairs g) := by
  have hh := decideAlignedBlocks_sound (forkBlocks g,alignmentPairs g) h
  exact ⟨(forkBlocks_spec g _).mp hh.1,hh.2⟩

/-- The actual aligned solver needs no stronger premise than an ordinary LR
partition, for every endpoint-valid raw graph (planar or otherwise). -/
theorem solveAlignedLR_complete (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (solveAlignedLR g).1 = true ↔ ∃ side, LRCondition g side := by
  rw [solveAlignedLR,decideAlignedBlocks_safe_complete _ (alignmentPairs_safe g hg)]
  exact exists_congr (fun side => forkBlocks_spec g side)

/-- Alignment does not alter the computed accept/reject decision. -/
theorem solveAlignedLR_flag (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (solveAlignedLR g).1 = (solveLR g).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [solveAlignedLR_complete g hg,solveLR_complete g]

end PlanarHom.PlanarityLRRawConstraints
