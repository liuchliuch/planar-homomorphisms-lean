import PlanarHom.FisherCubicReferenceMatching
import PlanarHom.FisherReferenceMachines

/-! NEW exact calibration sign of the explicit first-occurrence reference
matching. It equals the original literal pairing/canonical-sign definition. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph MultiGraph.Kasteleyn FisherNumericEnumeration
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
variable {K : Type} [CommRing K]

 theorem canonicalSign_reference (log : List ℕ) (e : Fin g.edges.length) :
    ((code g).toMultiGraph (valid g hg hc)).canonicalSign (R:=K)
      (fun e=>logOrientation log e.val) (referenceEdge g hg hc e)=referenceEdgeSign g log e.val := by
  simp only [canonicalSign,Fin.lt_def,referenceEdge_src,referenceEdge_dst,orientationSign,referenceEdge_val,referenceEdgeSign]

 theorem crossing_reference (e f : Fin g.edges.length) :
    (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc e)).1 <
      (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc f)).1 ∧
    (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc f)).1 <
      (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc e)).2 ∧
    (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc e)).2 <
      (((code g).toMultiGraph (valid g hg hc)).canonicalPair (referenceEdge g hg hc f)).2 ↔
      referenceCross g e.val f.val=true := by
  simp only [canonicalPair,Fin.lt_def]
  change (min _ _ < min _ _ ∧ min _ _ < max _ _ ∧ max _ _ < max _ _) ↔ _
  rw [referenceEdge_src,referenceEdge_dst,referenceEdge_src,referenceEdge_dst]
  simp [referenceCross,referenceLower,referenceUpper]

 theorem referenceSign_eq (log : List ℕ) :
    referenceSign (K:=K) g log=((code g).toMultiGraph (valid g hg hc)).matchingPfaffianSign
      (fun e=>logOrientation log e.val) (referenceMatching g hg hc) := by
  rw [matchingPfaffianSign_eq_products _ _ _ (referenceMatching_perfect g hg hc)]
  unfold referenceMatching
  rw [Finset.prod_image (referenceEdge_injective g hg hc).injOn,
    Finset.prod_image (referenceEdge_injective g hg hc).injOn]
  simp_rw [Finset.prod_image (referenceEdge_injective g hg hc).injOn]
  simp_rw [crossing_reference g hg hc,canonicalSign_reference g hg hc]
  unfold referenceSign
  rw [←List.map_coe_finRange g.edges.length]
  simp only [List.map_map,List.flatMap_map,Function.comp_def,List.flatMap_def,List.prod_flatten,List.map_map]
  simp only [Function.comp_def,←Fin.prod_univ_def]
  exact mul_comm _ _

end PlanarHom.FisherCubicCode
