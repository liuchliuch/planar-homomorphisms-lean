import PlanarHom.PlanarityLRNecessityReturnCuts
import PlanarHom.PlanarityLRPortRankSublist
import PlanarHom.PlanarityLRDirectedSubtreeRanks
import PlanarHom.PlanarityLRPlanarContourNecessity

/-! NEW actual DFS return-side forcing from the two literal subtree intervals.
No fork-side relation is assumed; the Boolean comparison is forced by the
proved nonalternation of the original paired occurrence ports. -/
noncomputable section
namespace PlanarHom.PlanarityLRNecessity
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityDepthFirstSearch
open PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRRealization

theorem return_pair_forced_side_at_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (hnonalt : RootPortsNonalternating g hg rows)
    (r v : Fin g.vertices) (hr : height g r.val=0) (hv : 0<height g v.val)
    (hroot : componentRoot g v.val=r.val) (e f : ℕ) (he : e∈outgoing g v.val) (hf : f∈outgoing g v.val)
    (b c : Fin g.edges.length) (hb : b.val∈returns g e) (hc : c.val∈returns g f)
    (hcb : targetHeight g c.val<targetHeight g b.val)
    (hbm : ∀ s, (b,s)∈directedRootPorts g hg rows r)
    (hcm : ∀ s, (c,s)∈directedRootPorts g hg rows r) :
    decide ((directedRootPorts g hg rows r).idxOf (b,true)<(directedRootPorts g hg rows r).idxOf (b,false))=
      decide ((directedRootPorts g hg rows r).idxOf (c,true)<(directedRootPorts g hg rows r).idxOf (b,true)) := by
  classical
  let W := directedRootPorts g hg rows r
  have hcut := return_pair_cut_ancestry g hg he hf hb hc hcb
  have hbtvalid := (source_target_valid g hg b.isLt).2
  let p : Fin g.edges.length := ⟨parentEdge g v.val,parentEdge_lt g v.isLt hv⟩
  have hp := parentEdge_tree g hg v.isLt hv
  have hpt : target g p.val=v.val := hp.2.1
  have hpr : componentRoot g (source g p.val)=r.val :=
    (tree_componentRoot g hg hp.1).trans ((congrArg (componentRoot g) hpt).trans hroot)
  let q : Fin g.edges.length := ⟨parentEdge g (target g b.val),parentEdge_lt g hbtvalid hcut.2.2.2.2.2.2.1⟩
  have hq := parentEdge_tree g hg hbtvalid hcut.2.2.2.2.2.2.1
  have hqt : target g q.val=target g b.val := hq.2.1
  have htbv : Desc g (target g b.val) v.val := by
    simpa only [(outgoing_spec g he).2.2] using returns_target_desc_source g hg e hb
  have hqroot : componentRoot g (source g q.val)=r.val :=
    (tree_componentRoot g hg hq.1).trans ((congrArg (componentRoot g) hqt).trans
      ((componentRoot_eq_of_desc g v.isLt htbv).trans hroot))
  have hinner : (W.idxOf (b,false)<W.idxOf (b,true) ∧ W.idxOf (b,false)<W.idxOf (c,true)) ∨
      (W.idxOf (b,true)<W.idxOf (b,false) ∧ W.idxOf (c,true)<W.idxOf (b,false)) := by
    apply directedSubtreePorts_outside_rank g hg rows r hr p hp.1 hpr (b,true) (b,false) (c,true)
      (hbm true) (hbm false) (hcm true)
    · simpa only [hpt] using hcut.1
    · simpa only [hpt] using hcut.2.1
    · simpa only [hpt] using hcut.2.2.1
  have ho₁ : (W.idxOf (c,false)<W.idxOf (b,false) ∧ W.idxOf (c,false)<W.idxOf (b,true)) ∨
      (W.idxOf (b,false)<W.idxOf (c,false) ∧ W.idxOf (b,true)<W.idxOf (c,false)) := by
    apply directedSubtreePorts_outside_rank g hg rows r hr q hq.1 hqroot (b,false) (c,false) (b,true)
      (hbm false) (hcm false) (hbm true)
    · simpa only [hqt] using (show Desc g (target g b.val) (target g b.val) from Or.inl rfl)
    · simpa only [hqt] using hcut.2.2.2.1
    · simpa only [hqt] using hcut.2.2.2.2.2.1
  have ho₂ : (W.idxOf (c,false)<W.idxOf (b,true) ∧ W.idxOf (c,false)<W.idxOf (c,true)) ∨
      (W.idxOf (b,true)<W.idxOf (c,false) ∧ W.idxOf (c,true)<W.idxOf (c,false)) := by
    apply directedSubtreePorts_outside_rank g hg rows r hr q hq.1 hqroot (b,true) (c,false) (c,true)
      (hbm true) (hcm false) (hcm true)
    · simpa only [hqt] using hcut.2.2.2.1
    · simpa only [hqt] using hcut.2.2.2.2.1
    · simpa only [hqt] using hcut.2.2.2.2.2.1
  have hne : b≠c := fun h => hcut.2.2.2.2.2.2.2 (congrArg Fin.val h)
  have hn := pairNonalternating_of_word W (hnonalt r hr) b c hne hbm hcm
  have hs : W.idxOf (b,true)≠W.idxOf (c,true) := by
    simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
      idxOf_ne_of_mem_ne W (hbm true) (hcm true) (fun h => hne (congrArg Prod.fst h))
  exact forcedSide_of_nestedCuts W.idxOf b c hn hs hinner (three_inside_of_pairwise_outside ho₁ ho₂)

end PlanarHom.PlanarityLRNecessity
