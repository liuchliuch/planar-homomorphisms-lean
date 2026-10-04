import PlanarHom.FisherGlobalEuler
import PlanarHom.PlanarityRowGlobalEuler
import PlanarHom.PlanarityLRGlobalEulerIsolates
import PlanarHom.FisherInheritedRowSemantics
import PlanarHom.FisherInheritedEuler
import PlanarHom.FisherPipelineComponents

/-! NEW complete finite Euler proof for the actual serialized Fisher graph
and its realized inherited rows, from ordinary original-input planarity. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FisherInheritedRowCode
open Complexity MultiGraph MultiGraph.Kasteleyn Fisher PlanarityLRRealization FinitePermutationCycles
variable {g : MixedCode} {bt ut : ℕ} (hp : g.PlanarValid bt ut)

 theorem source_ordering_euler :
    Fintype.card (Fin g.vertices)+count (FisherContourOrder.ordering g hp.1).rotationRows.facePerm+
      Fintype.card (IsolatedVertex (FisherContourOrder.ordering g hp.1))=
      Fintype.card (Fin g.edges.length)+2*(g.toMultiGraph hp.1).componentCount Finset.univ := by
  let R:=directRotationRows g hp.1 (PlanarityLRConstraints.decideAligned g).2
  have hf : (FisherContourOrder.ordering g hp.1).rotationRows.facePerm=R.facePerm :=
    (ordering_face_decidable R.incidenceOrdering _ _).trans (incidenceOrdering_face R)
  have hi : Fintype.card (IsolatedVertex (FisherContourOrder.ordering g hp.1))=
      Fintype.card {v : Fin g.vertices // (g.toMultiGraph hp.1).selectedDegree Finset.univ v=0} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun v=>by rw [(FisherContourOrder.ordering g hp.1).degree_eq])
  rw [hf,hi,Fintype.card_fin,Fintype.card_fin]
  exact planar_global_euler_with_isolates g hp

 theorem typedExpansionRows_euler :
    (FisherCodePipeline.intermediate g).vertices+
      count (typedExpansionRows g hp.1 (FisherContourOrder.ordering g hp.1)
        (FisherContourOrder.computed_realizes g hp.1)).facePerm=
      (FisherCodePipeline.intermediate g).edges.length+
        2*((FisherCodePipeline.intermediate g).toMultiGraph (FisherCodePipeline.intermediate_valid hp.1)).componentCount Finset.univ := by
  rw [typedExpansionRows_eq_redecidable]
  have hh:=expansion_euler_global (FisherContourOrder.ordering g hp.1) (by
    apply (congrArg (fun k : ℕ=>Fintype.card (Fin g.vertices)+k+
      Fintype.card (IsolatedVertex (FisherContourOrder.ordering g hp.1))) ?_).trans (source_ordering_euler hp)
    exact congrArg count (ordering_face_decidable (FisherContourOrder.ordering g hp.1) _ _))
  have hr : Fintype.card (ExpansionVertex (FisherContourOrder.ordering g hp.1))+
      count (RotationRows.redecidable (Fisher.expansionRows (FisherContourOrder.ordering g hp.1))).facePerm=
      Fintype.card (ExpansionEdge (FisherContourOrder.ordering g hp.1))+
        2*(expansionGraph (FisherContourOrder.ordering g hp.1)).componentCount Finset.univ := by
    rw [RotationRows.redecidable_facePerm]
    exact hh
  simpa only [Fintype.card_fin] using
    (FisherExpansionCode.computedIncidenceEquiv g hp.1).dartRelabel.euler_global _ hr

 theorem typedInheritedRows_euler :
    (FisherCodePipeline.code g).vertices+count (typedInheritedRows g hp.1).facePerm=
      (FisherCodePipeline.code g).edges.length+
        2*((FisherCodePipeline.code g).toMultiGraph (FisherCodePipeline.valid hp.1)).componentCount Finset.univ := by
  let q:=FisherCodePipeline.intermediate g
  let hq:=FisherCodePipeline.intermediate_valid hp.1
  let hc:=FisherCodePipeline.intermediate_cubic hp.1
  let R:=typedExpansionRows g hp.1 (FisherContourOrder.ordering g hp.1) (FisherContourOrder.computed_realizes g hp.1)
  let p:=FisherCubicCode.ports q hq hc
  have hR : Fintype.card (Fin q.vertices)+count R.facePerm=
      Fintype.card (Fin q.edges.length)+2*(cubicOriginal p).componentCount Finset.univ := by
    rw [FisherCubicCode.cubicOriginal_ports,Fintype.card_fin,Fintype.card_fin]
    exact typedExpansionRows_euler hp
  have hh:=cubicInherited_euler_global p R hR
  have hr : Fintype.card (Fin q.vertices×Fin 3)+
      count (RotationRows.redecidable (cubicInheritedRows p R)).facePerm=
      Fintype.card (Fin q.edges.length⊕(Fin q.vertices×Fin 3))+
        2*(cubicDecoration p).componentCount Finset.univ := by
    rw [RotationRows.redecidable_facePerm]
    exact hh
  simpa only [Fintype.card_fin] using
    (FisherCubicCode.incidenceEquiv q hq hc).dartRelabel.euler_global _ hr

 theorem componentEuler : PlanarityRowFaceCode.ComponentEuler (FisherCodePipeline.code g)
    (FisherCodePipeline.valid hp.1) (typedInheritedRows g hp.1) :=
  PlanarityRowFaceCode.componentEuler_of_global _ _ _ (FisherCodePipeline.incident hp.1) (typedInheritedRows_euler hp)

end PlanarHom.FisherInheritedRowCode
