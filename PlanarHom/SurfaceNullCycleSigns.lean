import PlanarHom.SurfaceRotationFacePotentials
import PlanarHom.OccurrenceFiniteKasteleynCycle
import PlanarHom.OccurrenceKasteleynCycleFlipSigns

/-! NEW surface Kasteleyn correctness for actual null-homologous alternating
cycles. Only null-homology replaces the sphere Euler premise: the face cut,
normalization, region parity and matching confinement are all proved. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

def evenSubgraphCycle (A : Finset E) (hA : G.EvenSubgraph A) : R.cycleSpace :=
  ⟨edgeIndicator A,G.evenSubgraph_boundary_zero A hA⟩

theorem exists_faceCut_of_null (root : Dart E) (A : Finset E) (hA : G.EvenSubgraph A)
    (hnull : R.homologyClass (R.evenSubgraphCycle A hA)=0) : Nonempty (R.FaceCut A root) := by
  obtain ⟨f,hroot,hf⟩:=R.exists_normalized_face_potential_of_null root _ hnull
  refine ⟨⟨fun F=>decide (f F=1),by simp [hroot],?_⟩⟩
  intro e
  have he:=congrFun hf e
  rw [R.dualGraph.coboundaryMatrix_apply] at he
  change f (R.faceOf (e,true))-f (R.faceOf (e,false))=if e∈A then 1 else 0 at he
  change (decide (f (R.faceOf (e,true))=1) ^^ decide (f (R.faceOf (e,false))=1))=decide (e∈A)
  generalize hx : f (R.faceOf (e,true))=x at he ⊢
  generalize hy : f (R.faceOf (e,false))=y at he ⊢
  fin_cases x <;> fin_cases y <;> by_cases h:e∈A <;> norm_num [h] at *

/-- A genuine surface statement: no Euler-zero or geometric disk assumption. -/
theorem alternatingCycle_boundarySign_neg_one_of_null
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N : Finset E} (flip : AlternatingCycleFlip G M N)
    (hnull : R.homologyClass (R.evenSubgraphCycle flip.cycle.cycleEdges flip.cycle.evenSubgraph)=0) :
    boundarySign orientation flip.cycle.cycleDarts= -1 := by
  obtain ⟨C⟩:=R.exists_faceCut_of_null root _ _ hnull
  apply FaceCut.boundarySign_eq_neg_one flip.cycle C orientation flip.even_length
    flip.left_perfect.exists_dart_at (C.selectedFace_productLaw_of_except orientation hfaces)
  apply FaceCut.inside_card_even_of_matching flip.cycle C flip.left_perfect
  intro e he hv
  rcases hv with hs|ht
  · exact flip.left_incident_mem_cycle (G.src e) hs e he (by simp [endpointCount])
  · exact flip.left_incident_mem_cycle (G.dst e) ht e he (by simp [endpointCount])

end PlanarHom.PlanarityLRRealization.RotationRows
