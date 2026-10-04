import PlanarHom.PlanarityLRComponentGraph
import Mathlib.Data.List.NodupEquivFin

/-! NEW component Euler tree cardinality from the literal verified DFS tree lists. -/
noncomputable section
namespace PlanarHom.MultiGraph.RootedOccurrenceTree
variable {V E : Type*} {G : MultiGraph V E}

theorem vertices_eq_root_cons_dst_edges (tree : RootedOccurrenceTree V E) (ht : tree.Compatible G) :
    tree.vertices=tree.root::tree.edges.map G.dst := by
  induction tree using induction_children with
  | step v children ih =>
      rw [vertices_node,root_node,edges_node,List.map_flatMap]
      congr 1
      apply List.flatMap_congr
      intro c hc
      have hh:=(compatible_node _ _).mp ht c hc
      simpa only [List.map_cons,hh.2.1] using ih c hc hh.2.2

theorem valid_edges_nodup (tree : RootedOccurrenceTree V E) (ht : tree.Valid G) : tree.edges.Nodup := by
  have hn:=ht.2
  rw [vertices_eq_root_cons_dst_edges tree ht.1] at hn
  exact List.Nodup.of_map G.dst (List.nodup_cons.mp hn).2

theorem edges_length_add_one (tree : RootedOccurrenceTree V E) (ht : tree.Compatible G) :
    tree.edges.length+1=tree.vertices.length := by
  rw [vertices_eq_root_cons_dst_edges tree ht,List.length_cons,List.length_map]

end PlanarHom.MultiGraph.RootedOccurrenceTree
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

abbrev ComponentTreeEdge (g : MixedCode) (r : ℕ) :=
  {e:Fin g.edges.length // isTree g e.val=true ∧ componentRoot g (source g e.val)=r}

theorem card_list_members {A : Type*} (xs : List A) (hn : xs.Nodup) : Nat.card {a:A // a∈xs}=xs.length := by
  classical
  have hh:=Nat.card_congr (List.Nodup.getEquiv xs hn).symm
  simpa only [Nat.card_fin] using hh

def componentTreeVertexEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) :
    {v:Fin g.vertices // v∈(dfsTree g hg r).vertices} ≃ ComponentVertex g r.val where
  toFun v := ⟨v.val,(dfsTree_root_vertices g hg r v.val hr).mp v.property⟩
  invFun v := ⟨v.val,(dfsTree_root_vertices g hg r v.val hr).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def componentTreeEdgeEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) :
    {e:Fin g.edges.length // e∈(dfsTree g hg r).edges} ≃ ComponentTreeEdge g r.val where
  toFun e := ⟨e.val,(dfsTree_root_edges g hg r hr e.val).mp e.property⟩
  invFun e := ⟨e.val,(dfsTree_root_edges g hg r hr e.val).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def componentTreeEdgeSubtypeEquiv (g : MixedCode) (r : ℕ) :
    ComponentTreeEdge g r ≃ {e:ComponentEdge g r // isTree g e.val.val=true} where
  toFun e := ⟨⟨e.val,e.property.2⟩,e.property.1⟩
  invFun e := ⟨e.val.val,e.property,e.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem component_tree_edges_add_one (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) :
    Nat.card (ComponentTreeEdge g r.val)+1=Nat.card (ComponentVertex g r.val) := by
  rw [←Nat.card_congr (componentTreeEdgeEquiv g hg r hr),←Nat.card_congr (componentTreeVertexEquiv g hg r hr)]
  rw [card_list_members _ (RootedOccurrenceTree.valid_edges_nodup _ (dfsTree_valid g hg r)),
    card_list_members _ (dfsTree_valid g hg r).2]
  exact RootedOccurrenceTree.edges_length_add_one _ (dfsTree_valid g hg r).1

theorem component_selected_edges_add_one (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) :
    Nat.card {e:ComponentEdge g r.val // isTree g e.val.val=true}+1=Nat.card (ComponentVertex g r.val) := by
  rw [←Nat.card_congr (componentTreeEdgeSubtypeEquiv g r.val)]
  exact component_tree_edges_add_one g hg r hr

theorem component_isolated_card (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) [IsEmpty (ComponentEdge g r.val)] :
    Nat.card (ComponentVertex g r.val)=1 := by
  haveI : IsEmpty (ComponentTreeEdge g r.val) := ⟨fun e=>isEmptyElim (⟨e.val,e.property.2⟩ : ComponentEdge g r.val)⟩
  have hh:=component_tree_edges_add_one g hg r hr
  simpa using hh.symm

end PlanarHom.PlanarityLRRealization
