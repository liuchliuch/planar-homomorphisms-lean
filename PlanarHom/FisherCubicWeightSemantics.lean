import PlanarHom.FisherCubicCodeSemantics
import PlanarHom.FisherExpansionWeightSemantics

/-! NEW exact polynomial weight identity for the numeric triangle compiler.
Its canonical scan port order is related by literal occurrence bijections. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
local instance (priority := high) cubicWeightEdgeBEq : BEq (Fin g.edges.length⊕(Fin g.vertices×Fin 3)) := instBEqOfDecidableEq

 theorem incidenceEquiv_edge_val (e : Fin g.edges.length⊕(Fin g.vertices×Fin 3)) :
    ((incidenceEquiv g hg hc).edge e).val=(edgeList g).idxOf e := by
  change ((codeIncidenceEquiv (enumeratedCode_eq g hg hc) _ _).edge
    ((enumeratedIncidenceEquiv _ _ _ _ _ _ _).edge e)).val=_
  rw [codeIncidenceEquiv_edge_val]
  simp [enumeratedIncidenceEquiv,List.Nodup.getEquivOfForallMemList,List.idxOf,Lean.Grind.beq_eq_decide_eq]

 def typedWeight {K : Type} [Zero K] [One K] [Mul K] (x : List K) :
    Fin g.edges.length⊕(Fin g.vertices×Fin 3)→K :=
  Sum.elim (fun _=>1) (fun q=>
    portWeight x (eraseDart (ports g hg hc (q.1,triangle.src q.2))) *
    portWeight x (eraseDart (ports g hg hc (q.1,triangle.dst q.2))))

 theorem weights_eq_map {K : Type} [Zero K] [One K] [Mul K] (x : List K) :
    weights g x=(edgeList g).map (typedWeight g hg hc x) := by
  unfold weights edgeList
  rw [List.map_append,List.map_map,List.map_map]
  apply congrArg₂ List.append
  · simp only [typedWeight,Function.comp_def,Sum.elim_inl,List.map_const',List.length_range,List.length_finRange]
  · simp only [vertexList,SProd.sprod,List.product,List.map_flatMap,List.map_map]
    rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
    congr 1
    funext v
    rw [←List.map_coe_finRange 3,List.map_map]
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def,typedWeight,Sum.elim_inr]
    rw [←triangleSrc_eq i,←triangleDst_eq i,row_get_ports g hg hc v (triangle.src i),row_get_ports g hg hc v (triangle.dst i)]

 theorem weights_get {K : Type} [Zero K] [One K] [Mul K] (x : List K)
    (e : Fin g.edges.length⊕(Fin g.vertices×Fin 3)) :
    (weights g x).getD ((incidenceEquiv g hg hc).edge e).val 0=typedWeight g hg hc x e := by
  rw [incidenceEquiv_edge_val,weights_eq_map]
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
    getD_map_idxOf (edgeList g) (typedWeight g hg hc x) e (edgeList_mem g e) 0

 theorem matchingSum_weights {K : Type} [Semiring K] (φ : K→+*ℝ) (x : List K) :
    ((code g).toMultiGraph (valid g hg hc)).perfectMatchingSum (fun e=>φ ((weights g x).getD e.val 0))=
      (g.toMultiGraph hg).evenSubgraphSum (fun e=>φ (x.getD e.val 0)) := by
  rw [(incidenceEquiv g hg hc).perfectMatchingSum]
  have hw : ((fun e=>φ ((weights g x).getD e.val 0)) ∘ (incidenceEquiv g hg hc).edge)=
      cubicPolynomialWeight (ports g hg hc) (fun e=>φ (x.getD e.val 0)) := by
    funext e
    rw [Function.comp_apply,weights_get]
    cases e with
    | inl e => simp [typedWeight,cubicPolynomialWeight]
    | inr q =>
        simp only [typedWeight,cubicPolynomialWeight,Sum.elim_inr,map_mul,portWeight,Fisher.portWeight,eraseDart]
        split_ifs <;> simp
  rw [hw,←cubic_fisher_polynomial,cubicOriginal_ports]

end PlanarHom.FisherCubicCode
