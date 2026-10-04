import PlanarHom.PlanarityLRReturnRankSides
import PlanarHom.PlanarityLRReturnPortRanks
import PlanarHom.PlanarityLRReturnBlockSeparation

/-! NEW ordinary-input LR necessity. The side assignment is the actual rank
comparison of the two original occurrence ports in their computed component
root word. Literal subtree cuts and nonalternation force every fork block. -/
noncomputable section
namespace PlanarHom.PlanarityLRNecessity
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityDepthFirstSearch
open PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRRealization PlanarityLRConstraintBlocks

def contourSide (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (b : ℕ) : Bool :=
  if hb : b<g.edges.length then
    decide (directedPortRank g hg rows (⟨b,hb⟩,true)<directedPortRank g hg rows (⟨b,hb⟩,false))
  else false

theorem contourSide_eq_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices)
    (hroot : componentRoot g v.val=r.val) (e : ℕ) (he : e∈outgoing g v.val)
    (b : Fin g.edges.length) (hb : b.val∈returns g e) :
    contourSide g hg rows b.val=
      decide ((directedRootPorts g hg rows r).idxOf (b,true)<(directedRootPorts g hg rows r).idxOf (b,false)) := by
  unfold contourSide
  rw [dif_pos b.isLt]
  rw [outgoing_return_port_rank_eq_root g hg rows r v hroot e he b hb true,
    outgoing_return_port_rank_eq_root g hg rows r v hroot e he b hb false]

theorem contourSide_forced (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (hnonalt : RootPortsNonalternating g hg rows)
    (r v : Fin g.vertices) (hr : height g r.val=0) (hv : 0<height g v.val)
    (hroot : componentRoot g v.val=r.val) (e f : ℕ) (he : e∈outgoing g v.val) (hf : f∈outgoing g v.val)
    (b c : Fin g.edges.length) (hb : b.val∈returns g e) (hc : c.val∈returns g f)
    (hcb : targetHeight g c.val<targetHeight g b.val) :
    contourSide g hg rows b.val=
      decide ((directedRootPorts g hg rows r).idxOf (c,true)<(directedRootPorts g hg rows r).idxOf (b,true)) := by
  rw [contourSide_eq_root g hg rows r v hroot e he b hb]
  exact return_pair_forced_side_at_root g hg rows hnonalt r v hr hv hroot e f he hf b c hb hc hcb
    (outgoing_return_port_mem_root g hg rows r v hr hroot e he b hb)
    (outgoing_return_port_mem_root g hg rows r v hr hroot f hf c hc)

/-- All literal LR fork equations hold for the constructed actual comparison
bits. The two opposing monochromatic values come from the order of the two
whole outgoing return blocks in the same computed contour word. -/
theorem contourSide_isLR (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (hnonalt : RootPortsNonalternating g hg rows) :
    LRCondition g (contourSide g hg rows) := by
  intro v hv hpos e he f hf hfe
  let V : Fin g.vertices := ⟨v,hv⟩
  let r : Fin g.vertices := ⟨componentRoot g v,(componentRoot_spec g hv).1⟩
  have hr : height g r.val=0 := (componentRoot_spec g hv).2.2
  have hroot : componentRoot g V.val=r.val := rfl
  let E : Fin g.edges.length := ⟨e,outgoing_valid g v he⟩
  let F : Fin g.edges.length := ⟨f,outgoing_valid g v hf⟩
  have hEF : E≠F := fun h => hfe (congrArg Fin.val h).symm
  let W := directedRootPorts g hg rows r
  obtain ⟨left,hrank⟩ : ∃ left : Bool, ∀ b c : Fin g.edges.length,
      b.val∈returns g e → c.val∈returns g f →
      decide (W.idxOf (c,true)<W.idxOf (b,true))=left ∧
      decide (W.idxOf (b,true)<W.idxOf (c,true))=(!left) := by
    rcases returns_uniform_root_rank_order g hg rows r V hr hpos hroot E F he hf hEF with hord | hord
    · refine ⟨false,?_⟩
      intro b c hb hc
      have hh := hord b c hb hc
      exact ⟨decide_eq_false (not_lt_of_ge hh.le),decide_eq_true hh⟩
    · refine ⟨true,?_⟩
      intro b c hb hc
      have hh := hord b c hb hc
      exact ⟨decide_eq_true hh,decide_eq_false (not_lt_of_ge hh.le)⟩
  have hleft (b : ℕ) (hb : b∈(forkBlock g e f).1) : contourSide g hg rows b=left := by
    have hbr := (List.mem_filter.mp hb).1
    obtain ⟨c,hc,hcb⟩ := exists_shallower_return_of_fork g hg he hf hb
    let B : Fin g.edges.length := ⟨b,returns_valid g e hbr⟩
    let C : Fin g.edges.length := ⟨c,returns_valid g f hc⟩
    exact (contourSide_forced g hg rows hnonalt r V hr hpos hroot e f he hf B C hbr hc hcb).trans
      (hrank B C hbr hc).1
  have hright (c : ℕ) (hc : c∈(forkBlock g e f).2) : contourSide g hg rows c=(!left) := by
    have hcr := (List.mem_filter.mp hc).1
    have hc' : c∈(forkBlock g f e).1 := hc
    obtain ⟨b,hb,hbc⟩ := exists_shallower_return_of_fork g hg hf he hc'
    let B : Fin g.edges.length := ⟨b,returns_valid g e hb⟩
    let C : Fin g.edges.length := ⟨c,returns_valid g f hcr⟩
    exact (contourSide_forced g hg rows hnonalt r V hr hpos hroot f e hf he C B hcr hb hbc).trans
      (hrank B C hb hcr).2
  refine ⟨?_,?_,?_⟩
  · intro b hb c hc
    exact (hleft b hb).trans (hleft c hc).symm
  · intro b hb c hc
    exact (hright b hb).trans (hright c hc).symm
  · intro b hb c hc heq
    rw [hleft b hb,hright c hc] at heq
    exact Bool.self_ne_not left heq

/-- Ordinary planarity yields a genuine LR partition of the original computed
forks, with no supplied rotation, assignment, or planarity certificate. -/
theorem planar_exists_LRCondition (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    ∃ side : ℕ → Bool, LRCondition g side := by
  obtain ⟨rows,hnonalt⟩ := planar_exists_nonalternating_rows g hp
  exact ⟨contourSide g hp.1 rows,contourSide_isLR g hp.1 rows hnonalt⟩

theorem planar_solveLR_accepts (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    (solveLR g).1=true := (solveLR_complete g).mpr (planar_exists_LRCondition g hp)

theorem planar_solveAlignedLR_accepts (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    (solveAlignedLR g).1=true := (solveAlignedLR_complete g hp.1).mpr (planar_exists_LRCondition g hp)

end PlanarHom.PlanarityLRNecessity
