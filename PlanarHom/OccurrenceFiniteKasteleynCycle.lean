import PlanarHom.RotationSimpleCycleSigns
import PlanarHom.OccurrenceMatchingRegionParity
import PlanarHom.OccurrenceMatchingCycleConfinement

/-! NEW finite Kasteleyn alternating-cycle theorem. The face cut, its unique
selected boundary orbit, the relative Euler parity, and matching confinement
are all derived internally from literal rows, component Euler equality, and
ordinary perfect-matching incidence. No geometric disk certificate is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

/-- Every genuine alternating simple occurrence cycle is oddly oriented under
the face equations of a connected sphere rotation. Parallel two-cycles are
included. The component Euler identity is supplied by the computed LR proof. -/
theorem alternatingCycle_boundarySign_neg_one_of_euler
    (root : Dart E) (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (heuler : Fintype.card V+Fintype.card R.Face=Fintype.card E+2)
    (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N : Finset E} (flip : AlternatingCycleFlip G M N) :
    boundarySign orientation flip.cycle.cycleDarts= -1 := by
  obtain ⟨C⟩ := R.exists_faceCut root hG heuler flip.cycle.cycleEdges flip.cycle.evenSubgraph
  apply FaceCut.boundarySign_eq_neg_one flip.cycle C orientation flip.even_length
    flip.left_perfect.exists_dart_at (C.selectedFace_productLaw_of_except orientation hfaces)
  apply FaceCut.inside_card_even_of_matching flip.cycle C flip.left_perfect
  intro e he hv
  rcases hv with hs|ht
  · exact flip.left_incident_mem_cycle (G.src e) hs e he (by simp [endpointCount])
  · exact flip.left_incident_mem_cycle (G.dst e) ht e he (by simp [endpointCount])

end PlanarHom.PlanarityLRRealization.RotationRows
