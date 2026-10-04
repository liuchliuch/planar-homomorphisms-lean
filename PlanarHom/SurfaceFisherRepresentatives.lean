import PlanarHom.SurfaceFisherCycleProjection
import PlanarHom.SurfaceDartRelabelHomology
import PlanarHom.SurfaceCycleEdgeSets
import PlanarHom.SurfaceMatchingHomology
import PlanarHom.FisherCubicRotation
import PlanarHom.FisherMatchingBoundary

/-! NEW explicit representative matching for every closed Fisher chain.
Read its original-edge coordinates, form the actual even source subset, and
apply the literal cubic Fisher bijection. The difference has the same homology
class because the remaining chain is a sum of triangle face boundaries. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))

def cubicCycleProjection (c : (cubicInheritedRows p R).cycleSpace) : R.cycleSpace :=
  polygonExternalCycle R ((cubicRelabel p R).pullCycle (polygonRows R) c)

@[simp] theorem cubicCycleProjection_apply (c : (cubicInheritedRows p R).cycleSpace) (e : E) :
    (cubicCycleProjection p R c).val e=c.val (.inl e) := rfl

theorem cubic_homology_zero_of_external_zero (c : (cubicInheritedRows p R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) : (cubicInheritedRows p R).homologyClass c=0 := by
  apply ((cubicRelabel p R).pullCycle_homology_zero_iff (polygonRows R) c).mp
  apply polygon_homology_zero_of_external_zero
  intro e
  exact hz e

def cubicCycleRepresentative (c : (cubicInheritedRows p R).cycleSpace) : Finset (E⊕(V×Fin 3)) :=
  ((cubicFisherEquiv p) ⟨R.cycleEdgeSet (cubicCycleProjection p R c),R.cycleEdgeSet_even _⟩).val

theorem cubicCycleRepresentative_perfect (c : (cubicInheritedRows p R).cycleSpace) :
    (cubicDecoration p).PerfectMatching (cubicCycleRepresentative p R c) :=
  ((cubicFisherEquiv p) ⟨R.cycleEdgeSet (cubicCycleProjection p R c),R.cycleEdgeSet_even _⟩).property

theorem cubicCycleRepresentative_external (c : (cubicInheritedRows p R).cycleSpace) (e : E) :
    Sum.inl e∈cubicCycleRepresentative p R c ↔ c.val (.inl e)≠1 := by
  simp [cubicCycleRepresentative,cubicFisherEquiv,Equiv.coe_fn_mk,decoratedEdges,
    Finset.mem_disjSum,Finset.mem_compl,R.mem_cycleEdgeSet,cubicCycleProjection_apply]

def cubicRepresentativeDifference (c : (cubicInheritedRows p R).cycleSpace) :
    (cubicInheritedRows p R).cycleSpace :=
  (cubicInheritedRows p R).evenSubgraphCycle _
    ((cubicCycleRepresentative_perfect p R c).symmDiff_even (referenceMatching_perfect p))

theorem cubicRepresentativeDifference_external (c : (cubicInheritedRows p R).cycleSpace) (e : E) :
    (cubicRepresentativeDifference p R c).val (.inl e)=c.val (.inl e) := by
  have hr : (Sum.inl e : E⊕(V×Fin 3))∈referenceMatching := by
    simp [referenceMatching,decoratedEdges]
  simp only [cubicRepresentativeDifference,RotationRows.evenSubgraphCycle,edgeIndicator,
    Finset.mem_symmDiff,cubicCycleRepresentative_external,hr,not_true_eq_false,and_false,
    true_and,false_or,not_not]
  generalize c.val (.inl e)=z
  fin_cases z <;> decide

/-- An actual computable-form matching realizes the closed chain's quotient
class. No search for a matching or sign value is used in this construction. -/
theorem cubicCycleRepresentative_homology (c : (cubicInheritedRows p R).cycleSpace) :
    (cubicInheritedRows p R).matchingHomologyClass referenceMatching (referenceMatching_perfect p)
      (cubicCycleRepresentative p R c) (cubicCycleRepresentative_perfect p R c)=
      (cubicInheritedRows p R).homologyClass c := by
  have hz: (cubicInheritedRows p R).homologyClass (c+cubicRepresentativeDifference p R c)=0 := by
    apply cubic_homology_zero_of_external_zero p R
    intro e
    change c.val (.inl e)+(cubicRepresentativeDifference p R c).val (.inl e)=0
    rw [cubicRepresentativeDifference_external,ZModModule.add_self]
  rw [map_add,add_eq_zero_iff_eq_neg,ZModModule.neg_eq_self] at hz
  exact hz.symm

end PlanarHom.Fisher
