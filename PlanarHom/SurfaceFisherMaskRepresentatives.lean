import PlanarHom.SurfaceFisherMatchingMask
import PlanarHom.SurfaceBooleanRowSpanOn
import PlanarHom.SurfaceFisherRepresentatives
import PlanarHom.SurfaceRedecidableHomology
import PlanarHom.FisherCubicRowSemantics
import PlanarHom.FisherCubicReferenceMatching

/-! NEW literal raw Fisher matching masks realize the actual homology class
of each encoded closed chain. All occurrence positions and endpoint bits are
transported through the checked numeric incidence equivalence. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows MultiGraph MultiGraph.Kasteleyn Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
variable (R : RotationRows (g.toMultiGraph hg))

def maskMatching (bits : Row) : Finset (Fin (FisherCubicCode.code g).edges.length) :=
  Finset.univ.filter (fun e=>bitAt (mask g bits) e.val=true)

theorem maskMatching_map (bits : Row) : maskMatching g bits=
    (typedMatching g hg hc bits).map (FisherCubicCode.incidenceEquiv g hg hc).edge.toEmbedding := by
  ext e
  obtain ⟨a,rfl⟩:=(FisherCubicCode.incidenceEquiv g hg hc).edge.surjective e
  simp only [maskMatching,Finset.mem_filter,Finset.mem_univ,true_and,mask_get g hg hc,
    decide_eq_true_eq,Finset.mem_map,Equiv.toEmbedding_apply]
  exact ⟨fun h=>⟨a,h,rfl⟩,fun ⟨b,hb,hba⟩=>
    (FisherCubicCode.incidenceEquiv g hg hc).edge.injective hba ▸ hb⟩

theorem typedMatching_nil : typedMatching g hg hc []=Fisher.referenceMatching := by
  ext e
  cases e with
  | inl e => simp [typedMatching,sourceSet,bitAt,Fisher.referenceMatching,decoratedEdges]
  | inr q =>
    simp only [typedMatching,sourceSet,bitAt,List.getElem?_nil,Option.getD_none,
      Bool.false_eq_true,Finset.filter_false,Finset.compl_empty,Fisher.referenceMatching]
    simp [decoratedEdges,internalEdges,selectedPorts,triangleCompletion]

theorem maskMatching_reference_perfect :
    ((FisherCubicCode.code g).toMultiGraph (FisherCubicCode.valid g hg hc)).PerfectMatching
      (maskMatching g []) := by
  rw [maskMatching_map g hg hc,typedMatching_nil g hg hc]
  exact ((FisherCubicCode.incidenceEquiv g hg hc).perfectMatching_map_iff _).mpr
    (Fisher.referenceMatching_perfect _)

def pulledCycle (c : (FisherInheritedRowCode.typedCubicRows g hg hc R).cycleSpace) :
    (RotationRows.redecidable (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R)).cycleSpace :=
  ⟨fun e=>c.val ((FisherCubicCode.incidenceEquiv g hg hc).edge e),by
    change _=0
    funext v
    have hh:=(FisherCubicCode.incidenceEquiv g hg hc).dartRelabel.pullEdgeVector_boundary c.val v
    exact hh.trans (congrFun c.property ((FisherCubicCode.incidenceEquiv g hg hc).vertex v))⟩

theorem sourceSet_eq_projection (bits : Row)
    (c : (FisherInheritedRowCode.typedCubicRows g hg hc R).cycleSpace)
    (hb : finiteValue (FisherCubicCode.code g).edges.length bits=c.val) :
    sourceSet g bits=R.cycleEdgeSet
      (Fisher.cubicCycleProjection (FisherCubicCode.ports g hg hc) R (pulledCycle g hg hc R c)) := by
  ext e
  simp only [sourceSet,Finset.mem_filter,Finset.mem_univ,true_and,RotationRows.mem_cycleEdgeSet,
    Fisher.cubicCycleProjection_apply]
  have hv:=congrFun hb ((FisherCubicCode.incidenceEquiv g hg hc).edge (Sum.inl e))
  change bitValue (bitAt bits ((FisherCubicCode.referenceEdge g hg hc e).val))=
    (pulledCycle g hg hc R c).val (Sum.inl e) at hv
  rw [FisherCubicCode.referenceEdge_val] at hv
  rw [←hv]
  cases bitAt bits e.val <;> simp [bitValue]

theorem typedMatching_eq_representative (bits : Row)
    (c : (FisherInheritedRowCode.typedCubicRows g hg hc R).cycleSpace)
    (hb : finiteValue (FisherCubicCode.code g).edges.length bits=c.val) :
    typedMatching g hg hc bits=Fisher.cubicCycleRepresentative (FisherCubicCode.ports g hg hc) R
      (pulledCycle g hg hc R c) := by
  unfold typedMatching Fisher.cubicCycleRepresentative Fisher.cubicFisherEquiv
  simp only [Equiv.coe_fn_mk]
  rw [sourceSet_eq_projection g hg hc R bits c hb]
  congr 1
  · ext e
    simp
  · funext v
    congr 2
    ext e
    simp

theorem maskMatching_perfect (bits : Row)
    (c : (FisherInheritedRowCode.typedCubicRows g hg hc R).cycleSpace)
    (hb : finiteValue (FisherCubicCode.code g).edges.length bits=c.val) :
    ((FisherCubicCode.code g).toMultiGraph (FisherCubicCode.valid g hg hc)).PerfectMatching
      (maskMatching g bits) := by
  rw [maskMatching_map g hg hc,typedMatching_eq_representative g hg hc R bits c hb]
  exact ((FisherCubicCode.incidenceEquiv g hg hc).perfectMatching_map_iff _).mpr
    (Fisher.cubicCycleRepresentative_perfect _ _ _)


theorem maskMatching_homology (bits : Row)
    (c : (FisherInheritedRowCode.typedCubicRows g hg hc R).cycleSpace)
    (hb : finiteValue (FisherCubicCode.code g).edges.length bits=c.val) :
    (FisherInheritedRowCode.typedCubicRows g hg hc R).matchingHomologyClass
      (maskMatching g []) (maskMatching_reference_perfect g hg hc)
      (maskMatching g bits) (maskMatching_perfect g hg hc R bits c hb)=
      (FisherInheritedRowCode.typedCubicRows g hg hc R).homologyClass c := by
  let Rd:=FisherInheritedRowCode.typedCubicRows g hg hc R
  let diff : Rd.cycleSpace:=Rd.evenSubgraphCycle _
    ((maskMatching_perfect g hg hc R bits c hb).symmDiff_even (maskMatching_reference_perfect g hg hc))
  have hp : pulledCycle g hg hc R diff=
      Fisher.cubicRepresentativeDifference (FisherCubicCode.ports g hg hc) R (pulledCycle g hg hc R c) := by
    apply Subtype.ext
    funext e
    simp only [pulledCycle,diff,RotationRows.evenSubgraphCycle]
    change edgeIndicator _ ((FisherCubicCode.incidenceEquiv g hg hc).edge e)=_
    rw [maskMatching_map g hg hc bits,maskMatching_map g hg hc [],
      typedMatching_nil g hg hc,typedMatching_eq_representative g hg hc R bits c hb]
    simp only [Fisher.cubicRepresentativeDifference,RotationRows.evenSubgraphCycle,edgeIndicator,
      Finset.mem_symmDiff,Finset.mem_map,Equiv.toEmbedding_apply,
      (FisherCubicCode.incidenceEquiv g hg hc).edge.injective.eq_iff,exists_eq_right]
    rfl
  have hadd : pulledCycle g hg hc R (c+diff)=pulledCycle g hg hc R c+pulledCycle g hg hc R diff :=
    Subtype.ext rfl
  have ha:=Fisher.cubicCycleRepresentative_homology (FisherCubicCode.ports g hg hc) R (pulledCycle g hg hc R c)
  have hz : (RotationRows.redecidable
      (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R)).homologyClass
        (pulledCycle g hg hc R (c+diff))=0 := by
    apply (RotationRows.redecidable_homology_zero_iff _ _).mpr
    rw [hadd,hp,map_add]
    dsimp only [RotationRows.matchingHomologyClass] at ha
    dsimp only [Fisher.cubicRepresentativeDifference]
    rw [ha,ZModModule.add_self]
  have hn : Rd.homologyClass (c+diff)=0 := by
    apply ((FisherCubicCode.incidenceEquiv g hg hc).dartRelabel.pullCycle_homology_zero_iff
      (RotationRows.redecidable (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R)) (c+diff)).mp
    exact hz
  rw [map_add,add_eq_zero_iff_eq_neg,ZModModule.neg_eq_self] at hn
  exact hn.symm

end PlanarHom.SurfaceFisherMatching
