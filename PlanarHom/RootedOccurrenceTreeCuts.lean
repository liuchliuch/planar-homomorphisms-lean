import PlanarHom.RootedOccurrenceTree
import PlanarHom.OccurrenceKasteleynRootwardBoundary

/-! NEW literal subtree cut facts and their actual clipped geometric regions. -/
namespace PlanarHom.MultiGraph.RootedOccurrenceTree
variable {V E : Type*} {G : MultiGraph V E}

theorem induction_children {P : RootedOccurrenceTree V E → Prop}
    (step : ∀ v children, (∀ c∈children, P c.2) → P (.node v children))
    (tree : RootedOccurrenceTree V E) : P tree := by
  apply RootedOccurrenceTree.rec (motive_1:=P)
    (motive_2:=fun children => ∀ c∈children, P c.2) (motive_3:=fun c => P c.2)
    step (by simp) _ (fun _ _ h => h) tree
  intro head tail hh ht c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hh
  · exact ht c hc

theorem edge_endpoints_mem (tree : RootedOccurrenceTree V E) (ht : tree.Compatible G)
    (e : E) (he : e∈tree.edges) : G.src e∈tree.vertices ∧ G.dst e∈tree.vertices := by
  induction tree using induction_children with
  | step v children ih =>
      rw [edges_node] at he
      obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp he
      have hh := (compatible_node _ _).mp ht c hc
      rcases List.mem_cons.mp he with rfl | he
      · constructor
        · rw [hh.1]
          exact (node v children).root_mem_vertices
        · rw [hh.2.1,vertices_node]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,c.2.root_mem_vertices⟩)
      · have hh' := ih c hc hh.2.2 he
        rw [vertices_node]
        exact ⟨List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,hh'.1⟩),
          List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,hh'.2⟩)⟩

theorem child_vertices_disjoint {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) :
    children.Pairwise (fun c d => c.2.vertices.Disjoint d.2.vertices) := by
  have hv := ht.2
  rw [vertices_node,List.nodup_cons] at hv
  exact (List.nodup_flatMap.mp hv.2).2

theorem child_edges_nonincident_root {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (e : E) (he : e∈c.2.edges) : G.src e≠v ∧ G.dst e≠v := by
  have hh := c.2.edge_endpoints_mem (child_valid ht c hc).1 e he
  exact ⟨fun h => root_notMem_child ht c hc (h ▸ hh.1),
    fun h => root_notMem_child ht c hc (h ▸ hh.2)⟩

theorem branch_endpoints {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (e : E) (he : e∈c.1::c.2.edges) :
    (G.src e=v ∨ G.src e∈c.2.vertices) ∧ G.dst e∈c.2.vertices := by
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨Or.inl ((compatible_node _ _).mp ht.1 c hc).1,
      ((compatible_node _ _).mp ht.1 c hc).2.1 ▸ c.2.root_mem_vertices⟩
  · have hh := c.2.edge_endpoints_mem (child_valid ht c hc).1 e he
    exact ⟨Or.inr hh.1,hh.2⟩

theorem branch_edges_disjoint {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) :
    children.Pairwise (fun c d => (c.1::c.2.edges).Disjoint (d.1::d.2.edges)) := by
  apply (child_vertices_disjoint ht).imp_of_mem
  intro c d hc hd hdisj e he hf
  exact hdisj (branch_endpoints ht c hc e he).2 (branch_endpoints ht d hd e hf).2

end PlanarHom.MultiGraph.RootedOccurrenceTree

noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

/-- The exact region available to a child branch, including its upward band. -/
def branchRegion (c : E × RootedOccurrenceTree V E) : Set Plane :=
  C.clippedRegion {v | v∈c.2.vertices} {e | e∈c.1::c.2.edges}

theorem branchRegions_disjoint {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) :
    children.Pairwise (fun c d => Disjoint (C.branchRegion c) (C.branchRegion d)) := by
  apply ((child_vertices_disjoint ht).and (branch_edges_disjoint ht)).imp_of_mem
  intro c d hc hd hh
  apply C.clippedRegions_disjoint
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => hh.1 h₁ h₂)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => hh.2 h₁ h₂)
  · intro e he
    have he' := branch_endpoints ht c hc e he
    constructor
    · intro hs
      rcases he'.1 with hs' | hs'
      · exact root_notMem_child ht d hd (hs' ▸ hs)
      · exact hh.1 hs' hs
    · exact fun hs => hh.1 he'.2 hs
  · intro e he
    have he' := branch_endpoints ht d hd e he
    constructor
    · intro hs
      rcases he'.1 with hs' | hs'
      · exact root_notMem_child ht c hc (hs' ▸ hs)
      · exact hh.1 hs hs'
    · exact fun hs => hh.1 hs he'.2

theorem branchRegion_disjoint_external_disk {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (w : V) (hw : w∉(node v children).vertices) :
    Disjoint (C.branchRegion c) (C.hostDisk w) := by
  have hvw : v≠w := fun h => hw (h ▸ (node v children).root_mem_vertices)
  have hchild : w∉c.2.vertices := by
    intro h
    apply hw
    rw [vertices_node]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,h⟩)
  apply C.clippedRegion_disjoint_disk w hchild
  intro e he
  have hh := branch_endpoints ht c hc e he
  constructor
  · intro h
    rcases hh.1 with hs | hs
    · exact hvw (hs.symm.trans h)
    · exact hchild (h ▸ hs)
  · exact fun h => hchild (h ▸ hh.2)

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
