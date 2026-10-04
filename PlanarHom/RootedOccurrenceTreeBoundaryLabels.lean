import PlanarHom.RootedOccurrenceTreeLookup

/-! NEW finite endpoint/exclusion bookkeeping for child boundary labels. -/
namespace PlanarHom.MultiGraph.RootedOccurrenceTree
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {v : V} {cs : List (E×RootedOccurrenceTree V E)}

 theorem child_vertex_mem_node (c : E×RootedOccurrenceTree V E) (hc : c∈cs) {w : V}
    (hw : w∈c.2.vertices) : w∈(node v cs).vertices := by
  rw [vertices_node]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,hw⟩)

 theorem child_branch_edge_mem_node (c : E×RootedOccurrenceTree V E) (hc : c∈cs) {e : E}
    (he : e∈c.1::c.2.edges) : e∈(node v cs).edges := by
  rw [edges_node]
  exact List.mem_flatMap.mpr ⟨c,hc,he⟩

 theorem dart_host_endpoints (a : Dart E) :
    (G.dartPair a).1=G.src a.1 ∨ (G.dartPair a).1=G.dst a.1 := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [dartPair]

 theorem child_boundary_avoids_node (ht : (node v cs).Valid G) (parent : E)
    (hdst : G.dst parent=v) (hsrc : G.src parent∉(node v cs).vertices)
    (c : E×RootedOccurrenceTree V E) (hc : c∈cs) (a : Dart E)
    (hhost : (G.dartPair a).1∈c.2.vertices) (hedge : a.1∉c.1::c.2.edges) :
    a.1∉parent::(node v cs).edges := by
  intro he
  rcases List.mem_cons.mp he with he | he
  · rcases dart_host_endpoints (G:=G) a with hs | hd
    · rw [he] at hs
      exact hsrc (child_vertex_mem_node c hc (hs ▸ hhost))
    · rw [he,hdst] at hd
      exact root_notMem_child ht c hc (hd ▸ hhost)
  · rw [edges_node] at he
    obtain ⟨k,hk,he⟩:=List.mem_flatMap.mp he
    by_cases hck:c=k
    · subst k
      exact hedge he
    · have hdis: c.2.vertices.Disjoint k.2.vertices :=
        (child_vertices_disjoint ht).forall (fun _ _ h=>h.symm) hc hk hck
      have hends:=branch_endpoints ht k hk a.1 he
      rcases dart_host_endpoints (G:=G) a with hs | hd
      · rcases hends.1 with hs' | hs'
        · exact root_notMem_child ht c hc ((hs.trans hs') ▸ hhost)
        · exact hdis hhost (hs.symm ▸ hs')
      · exact hdis hhost (hd.symm ▸ hends.2)

 theorem child_edge_ne_external_parent (ht : (node v cs).Valid G) (parent : E)
    (hsrc : G.src parent∉(node v cs).vertices) (c : E×RootedOccurrenceTree V E) (hc : c∈cs) : c.1≠parent := by
  intro he
  have hs:=((compatible_node _ _).mp ht.1 c hc).1
  rw [he] at hs
  exact hsrc (hs.symm ▸ (node v cs).root_mem_vertices)

end PlanarHom.MultiGraph.RootedOccurrenceTree
