import PlanarHom.PlanarityLRDirectedSubtreeRanks

/-! NEW actual root-word membership for every non-tree port in its DFS component. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch

theorem mem_directedRootPorts_of_component (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (a : Dart (Fin g.edges.length)) (ha : isTree g a.1.val=false)
    (hroot : componentRoot g ((dfsGraph g hg).dartPair a).1.val=r.val) :
    a∈directedRootPorts g hg rows r := by
  let v := ((dfsGraph g hg).dartPair a).1
  by_cases hz : height g v.val=0
  · have hv : v=r := Fin.ext ((componentRoot_eq_self g v.isLt hz).symm.trans hroot)
    rw [directedRootPorts_eq_row_expansion g hg rows r hr]
    refine List.mem_flatMap.mpr ⟨a,(rows.mem _ _).mpr hv,?_⟩
    simp [directedRootBlock,ha]
  · have hp := Nat.pos_of_ne_zero hz
    let p : Fin g.edges.length := ⟨parentEdge g v.val,parentEdge_lt g v.isLt hp⟩
    have ht := parentEdge_tree g hg v.isLt hp
    have htarget : target g p.val=v.val := ht.2.1
    have hpr : componentRoot g (source g p.val)=r.val :=
      (tree_componentRoot g hg ht.1).trans ((congrArg (componentRoot g) htarget).trans hroot)
    apply (directedSubtreePorts_infix_root g hg rows r hr p ht.1 hpr).sublist.subset
    apply (mem_directedSubtreePorts g hg rows p ht.1 a).mpr
    apply (directedSubtreeKeep_eq_true g hg p a).mpr
    exact ⟨ha,Or.inl htarget⟩

end PlanarHom.PlanarityLRRealization
