import PlanarHom.OccurrenceMatchingRegionParity
import PlanarHom.OccurrenceMatchingCycleIncidence

/-! NEW occurrence-sensitive disjoint simple-cycle families. This is only the
finite contour input: a separate theorem constructs it from actual matchings. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E]

structure CycleBoundaryFamily (G : MultiGraph V E) (A : Finset E) (n : ℕ) where
  cycle : Fin n→DirectedSimpleCycle G
  vertex_disjoint : ∀i j,i≠j→Disjoint (cycle i).cycleVertices (cycle j).cycleVertices
  edge_cover : ∀e,e∈A↔∃i,e∈(cycle i).cycleEdges

namespace CycleBoundaryFamily
variable {G : MultiGraph V E} {A : Finset E} {n : ℕ} (F : CycleBoundaryFamily G A n)

theorem vertex_index_unique {i j : Fin n} {v : V}
    (hi : v∈(F.cycle i).cycleVertices) (hj : v∈(F.cycle j).cycleVertices) : i=j := by
  by_contra h
  exact Finset.disjoint_left.mp (F.vertex_disjoint i j h) hi hj

theorem cycle_edge_mem (i : Fin n) {e : E} (he : e∈(F.cycle i).cycleEdges) : e∈A :=
  (F.edge_cover e).mpr ⟨i,he⟩

theorem cycle_dart_mem (i : Fin n) (j : Fin (F.cycle i).length) : ((F.cycle i).dart j).1∈A :=
  F.cycle_edge_mem i (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

theorem cycle_vertex_mem (i : Fin n) (j : Fin (F.cycle i).length) :
    (F.cycle i).vertex j∈(F.cycle i).cycleVertices :=
  Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem incident_cycle_edge (i : Fin n) (a : Dart E) (ha : a.1∈A)
    (hv : (G.dartPair a).1∈(F.cycle i).cycleVertices) : a.1∈(F.cycle i).cycleEdges := by
  obtain ⟨j,hj⟩:=(F.edge_cover a.1).mp ha
  have he:=F.vertex_index_unique hv ((F.cycle j).vertex_mem_of_incident a hj)
  exact he.symm ▸ hj

theorem selected_incident_at_next (i : Fin n) (j : Fin (F.cycle i).length) (a : Dart E)
    (ha : a.1∈A)
    (hv : (G.dartPair a).1=(F.cycle i).vertex (cycleNext _ (F.cycle i).length_ge_two j)) :
    a=reversePerm E ((F.cycle i).dart j) ∨
      a=(F.cycle i).dart (cycleNext _ (F.cycle i).length_ge_two j) :=
  (F.cycle i).incident_at_next j a
    (F.incident_cycle_edge i a ha (hv ▸ F.cycle_vertex_mem i _)) hv

theorem vertex_has_boundary (i : Fin n) {v : V} (hv : v∈(F.cycle i).cycleVertices) :
    ∃a : Dart E,a.1∈A ∧ (G.dartPair a).1=v := by
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hv
  exact ⟨(F.cycle i).dart j,F.cycle_dart_mem i j,(F.cycle i).tail_eq j⟩

theorem boundary_has_vertex (a : Dart E) (ha : a.1∈A) :
    ∃i,(G.dartPair a).1∈(F.cycle i).cycleVertices := by
  obtain ⟨i,hi⟩:=(F.edge_cover a.1).mp ha
  exact ⟨i,(F.cycle i).vertex_mem_of_incident a hi⟩

end CycleBoundaryFamily
end PlanarHom.MultiGraph
