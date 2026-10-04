import PlanarHom.RadialPottsCoefficientStates
import PlanarHom.RadialPottsLocalBoundary
import PlanarHom.PottsCenteredPathAlgebra

/-! NEW reconstruction: every Boolean tile state has its actual occurrence
multigraph, with a proved edge bijection, degree two and exact weighted value. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsTile.OnionBoundary PottsCentered
variable {E : Type} [Fintype E] {k : ℕ}

abbrev StateEdge (E : Type) (k : ℕ) := E × (Long k ⊕ HalfShort k)

def stateGraph (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) (k : ℕ) :
    MultiGraph (Vertex E k) (StateEdge E k) where
  src p := embed rotation p.1 ((localGraph k (choice p.1)).src p.2)
  dst p := embed rotation p.1 ((localGraph k (choice p.1)).dst p.2)

def stateEdgeMap (choice : E → Bool) (p : StateEdge E k) : E × RadialPottsTile.Edge k :=
  (p.1,match p.2 with | .inl e => .inl e | .inr e => .inr (e,choice p.1))

theorem stateEdgeMap_injective (choice : E → Bool) : Function.Injective (@stateEdgeMap E k choice) := by
  rintro ⟨e,f⟩ ⟨e',f'⟩ h
  have he := congrArg (fun p : E × RadialPottsTile.Edge k => p.1) h
  change e=e' at he
  subst e'
  have hf := congrArg (fun p : E × RadialPottsTile.Edge k => p.2) h
  cases f <;> cases f' <;> simp_all [stateEdgeMap]

@[simp] theorem stateEdgeMap_mem (choice : E → Bool) (p : StateEdge E k) :
    stateEdgeMap choice p∈stateEdges choice := by
  rcases p with ⟨e,f | f⟩ <;> simp [stateEdgeMap,stateEdges]

theorem stateEdges_image (choice : E → Bool) :
    @Finset.image (StateEdge E k) (E × RadialPottsTile.Edge k) (Classical.decEq _)
      (stateEdgeMap choice) Finset.univ=stateEdges choice := by
  letI : DecidableEq (E × RadialPottsTile.Edge k) := Classical.decEq _
  ext p
  constructor
  · intro h
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
    exact stateEdgeMap_mem choice a
  · intro h
    rcases p with ⟨e,f | ⟨f,b⟩⟩
    · exact Finset.mem_image.mpr ⟨(e,.inl f),Finset.mem_univ _,rfl⟩
    · have hb : b=choice e := by simpa [stateEdges] using h
      subst b
      exact Finset.mem_image.mpr ⟨(e,.inr f),Finset.mem_univ _,rfl⟩

@[simp] theorem stateEdgeMap_src (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (p : StateEdge E k) :
    (graph rotation k).src (stateEdgeMap choice p)=(stateGraph rotation choice k).src p := by
  rcases p with ⟨e,f | f⟩ <;> cases hc : choice e <;>
    simp [graph,stateGraph,stateEdgeMap,localGraph,blueGraph,switchedRedGraph,withShort,RadialPottsTile.graph,hc]

@[simp] theorem stateEdgeMap_dst (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (p : StateEdge E k) :
    (graph rotation k).dst (stateEdgeMap choice p)=(stateGraph rotation choice k).dst p := by
  rcases p with ⟨e,f | f⟩ <;> cases hc : choice e <;>
    simp [graph,stateGraph,stateEdgeMap,localGraph,blueGraph,switchedRedGraph,withShort,RadialPottsTile.graph,hc]

/-- Every vertex of the actual selected occurrence graph has degree exactly two. -/
theorem stateGraph_degree_two (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (v : Vertex E k) :
    (stateGraph rotation choice k).selectedDegree Finset.univ v=2 := by
  have hi := selectedDegree_image (stateGraph rotation choice k) (graph rotation k)
    (stateEdgeMap choice) (by intro p v; simp only [endpointCount, stateEdgeMap_src, stateEdgeMap_dst]; split_ifs <;> rfl) Finset.univ
    (stateEdgeMap_injective choice).injOn v
  rw [stateEdges_image] at hi
  rw [← hi]
  cases v with
  | inl p => exact state_white_degree rotation choice p.1 p.2
  | inr p => exact state_port_degree rotation choice p

/-- Exact selected contribution, retaining its actual vertex normalization. -/
theorem selectedValue_stateGraph (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (q : ℕ) :
    selectedValue (graph rotation k) q (stateEdges choice)=
      (q:ℚ)⁻¹^Fintype.card (Vertex E k)*(stateGraph rotation choice k).unweighted (interactionMatrix q) := by
  letI : DecidableEq (E × RadialPottsTile.Edge k) := Classical.decEq _
  unfold selectedValue
  rw [MultiGraph.unweighted_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [← stateEdges_image]
  rw [Finset.prod_image (stateEdgeMap_injective choice).injOn]
  apply Finset.prod_congr rfl
  intro p _
  rw [stateEdgeMap_src,stateEdgeMap_dst]
  rfl
end PlanarHom.RadialPotts.Assembly
