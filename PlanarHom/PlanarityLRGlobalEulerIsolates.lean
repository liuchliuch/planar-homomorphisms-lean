import PlanarHom.PlanarityLRIsolatedRoots

/-! Ordinary global Euler for the actual computed rows, retaining exactly one
isolated-vertex correction per empty DFS component and no virtual face cycle. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph PlanarityLRDirect FinitePermutationCycles

 theorem planar_component_euler_with_isolate (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut)
    (r : Root g) :
    Nat.card (ComponentVertex g r.val.val)+
      count (componentFace g hp.1 r.val.val (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2))+
      (if IsEmpty (ComponentEdge g r.val.val) then 1 else 0)=Nat.card (ComponentEdge g r.val.val)+2 := by
  by_cases he : IsEmpty (ComponentEdge g r.val.val)
  · letI := he
    letI : Nonempty (ComponentVertex g r.val.val) :=
      ⟨⟨r.val,componentRoot_eq_self g r.val.isLt r.property⟩⟩
    have hv := vertex_card_one_of_connected_empty (componentGraph g hp.1 r.val.val)
      (componentGraph_connected g hp.1 r.val r.property)
    have hE : Nat.card (ComponentEdge g r.val.val)=0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [if_pos he,hv,hE,count_empty]
  · have hn : Nonempty (ComponentEdge g r.val.val) := by
      by_contra h
      exact he ⟨fun e => h ⟨e⟩⟩
    letI := hn
    rw [if_neg he,add_zero]
    exact planar_computed_component_euler g hp r.val r.property

/-- Includes arbitrary disconnected graphs and the graph with no vertices. -/
theorem planar_global_euler_with_isolates (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    g.vertices+count (globalRowFace g hp.1 (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2))+
      Fintype.card {v : Fin g.vertices // (g.toMultiGraph hp.1).selectedDegree Finset.univ v=0}=
      g.edges.length+2*(g.toMultiGraph hp.1).componentCount Finset.univ := by
  have hs := Finset.sum_congr rfl (fun r (_ : r∈(Finset.univ : Finset (Root g))) =>
    planar_component_euler_with_isolate g hp r)
  have hv := vertices_eq_sum_components g
  have he := edges_eq_sum_components g hp.1
  have hc := componentCount_eq_roots g hp.1
  have hf := face_count_eq_sum_components g hp.1
    (directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2)
  have hi := isolated_card_eq_sum_roots g hp.1
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  omega
end PlanarHom.PlanarityLRRealization
