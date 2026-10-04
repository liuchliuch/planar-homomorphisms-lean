import PlanarHom.PlanarityLRTreePortWordUniqueness
import PlanarHom.PlanarityLRDirectedRowChildren
import PlanarHom.PlanarityLRGeometricRotationRows

/-! NEW identification of the geometric recursion's exact child blocks with
literal computed DFS children. No geometric order is assumed. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch
open MultiGraph.PolygonalDrawing.TwoSidedStripData
open MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

abbrev computedChildPairs (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :=
  (dfsChildren g v).map (fun e => (e,dfsTree g hg (dfsTarget g hg e)))

theorem exists_computedChildPair (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (e : Fin g.edges.length) :
    (∃ t, (e,t)∈computedChildPairs g hg v) ↔ e∈dfsChildren g v := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨f,hf,hft⟩ := List.mem_map.mp ht
    have he : f=e := congrArg Prod.fst hft
    exact he ▸ hf
  · intro h
    exact ⟨dfsTree g hg (dfsTarget g hg e),List.mem_map.mpr ⟨e,h,rfl⟩⟩

variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable {d : PolygonalDrawing (dfsGraph g hg)} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart (Fin g.edges.length) → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))
variable (charts : ∀ v, HostFanChart F v)

def dfsGeometricRows : RotationRows (dfsGraph g hg) := geometricRotationRows F charts

theorem geometric_childWordBlock_node (parent : Fin g.edges.length) (hp : isTree g parent.val=true)
    (branch : Fin g.edges.length → List (Dart (Fin g.edges.length)))
    (a : HostDart (dfsGraph g hg) (dfsTarget g hg parent)) :
    childWordBlock (computedChildPairs g hg (dfsTarget g hg parent))
        (fun c _ => branch c.1) (some parent) a =
      if a.val.1=parent then [] else if isTree g a.val.1.val then branch a.val.1 else [a.val] := by
  classical
  unfold childWordBlock
  by_cases hpar : a.val.1=parent
  · simp only [hpar,if_pos,Option.some.injEq]
  · have hpar' : ¬some parent=some a.val.1 := by simpa only [Option.some.injEq,eq_comm] using hpar
    rw [if_neg hpar',if_neg hpar]
    by_cases hc : ∃ t, (a.val.1,t)∈computedChildPairs g hg (dfsTarget g hg parent)
    · rw [dif_pos hc]
      have ht := ((dfsChildren_mem g _ _).mp ((exists_computedChildPair g hg _ _).mp hc)).1
      rw [ht]
      rfl
    · rw [dif_neg hc]
      have ht : isTree g a.val.1.val=false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        rcases directed_tree_at_target_cases g hg parent hp a.val ht a.property with h | h
        · exact hpar (congrArg Prod.fst h)
        · exact hc ((exists_computedChildPair g hg _ _).mpr h)
      rw [ht]
      rfl

theorem geometric_nodeWordExpansion (parent : Fin g.edges.length) (hp : isTree g parent.val=true)
    (branch : Fin g.edges.length → List (Dart (Fin g.edges.length))) :
    nodeWordExpansion charts (dfsTarget g hg parent) (computedChildPairs g hg (dfsTarget g hg parent))
        (fun c _ => branch c.1) parent rfl =
      afterParentInputs ((dfsGeometricRows g hg F charts).row (dfsTarget g hg parent)) (parent,false)
        (fun a => if a.1=parent then [] else if isTree g a.1.val then branch a.1 else [a]) := by
  classical
  unfold nodeWordExpansion dfsGeometricRows geometricRotationRows HostFanChart.dartRow
  dsimp only
  rw [afterParentInputs_map_embedding Subtype.val Subtype.val_injective
    (charts (dfsTarget g hg parent)).row (⟨(parent,false),rfl⟩ : HostDart (dfsGraph g hg) (dfsTarget g hg parent))]
  congr 1
  funext a
  exact geometric_childWordBlock_node g hg parent hp branch a

theorem geometric_childWordBlock_root (r : Fin g.vertices) (hr : height g r.val=0)
    (branch : Fin g.edges.length → List (Dart (Fin g.edges.length)))
    (a : HostDart (dfsGraph g hg) r) :
    childWordBlock (computedChildPairs g hg r) (fun c _ => branch c.1) none a =
      if isTree g a.val.1.val then branch a.val.1 else [a.val] := by
  classical
  unfold childWordBlock
  rw [if_neg (by simp)]
  by_cases hc : ∃ t, (a.val.1,t)∈computedChildPairs g hg r
  · rw [dif_pos hc]
    have ht := ((dfsChildren_mem g _ _).mp ((exists_computedChildPair g hg _ _).mp hc)).1
    rw [ht]
    rfl
  · rw [dif_neg hc]
    have ht : isTree g a.val.1.val=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hc ((exists_computedChildPair g hg _ _).mpr (directed_tree_at_root_child g hg r hr a.val ht a.property))
    rw [ht]
    rfl

theorem geometric_rootWordExpansion (r : Fin g.vertices) (hr : height g r.val=0)
    (branch : Fin g.edges.length → List (Dart (Fin g.edges.length))) :
    rootWordExpansion charts r (computedChildPairs g hg r) (fun c _ => branch c.1) =
      ((dfsGeometricRows g hg F charts).row r).flatMap
        (fun a => if isTree g a.1.val then branch a.1 else [a]) := by
  classical
  unfold rootWordExpansion dfsGeometricRows geometricRotationRows HostFanChart.dartRow
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro a _
  exact geometric_childWordBlock_root g hg r hr branch a

end PlanarHom.PlanarityLRRealization
