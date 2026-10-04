import PlanarHom.FisherExpansionCodeSemantics
import PlanarHom.FisherIncidenceAlgebra
import PlanarHom.FisherExpansionCorrespondence

/-! NEW exact transport of every emitted expansion weight, including all
path/loop unit factors and arbitrary signed or zero original values. -/
noncomputable section
open Classical
namespace PlanarHom.FisherNumericEnumeration
 theorem getD_map_idxOf {A B : Type} (xs : List A) (w : A→B) (a : A) (ha : a∈xs) (d : B) :
    (xs.map w).getD (xs.idxOf a) d=w a := by
  have hi:=List.idxOf_lt_length_iff.mpr ha
  simp [List.getD_eq_getElem?_getD,hi,List.getElem_idxOf]
end PlanarHom.FisherNumericEnumeration

namespace PlanarHom.FisherExpansionCode
open Complexity MultiGraph Fisher FisherNumericEnumeration
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)
variable {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)
local instance (priority := high) expansionWeightEdgeBEq : BEq (ExpansionEdge o) := instBEqOfDecidableEq

 theorem incidenceEquiv_edge_val (e : ExpansionEdge o) :
    ((incidenceEquiv g hg o hr).edge e).val=(edgeList g hg o).idxOf e := by
  change ((codeIncidenceEquiv (enumeratedCode_eq g hg o hr) _ _).edge
    ((enumeratedIncidenceEquiv _ _ _ _ _ _ _).edge e)).val=_
  rw [codeIncidenceEquiv_edge_val]
  simp [enumeratedIncidenceEquiv,List.Nodup.getEquivOfForallMemList,List.idxOf,Lean.Grind.beq_eq_decide_eq]

 def typedWeight {K : Type} [Zero K] [One K] (x : List K) : ExpansionEdge o→K :=
  Sum.elim (fun e=>x.getD e.val 0) (fun _=>1)

 include hr in
 theorem weights_eq_map {K : Type} [Zero K] [One K] (x : List K) :
    weights g rows x=(edgeList g hg o).map (typedWeight g hg o x) := by
  unfold weights edgeList
  rw [List.map_append,List.map_map,List.map_map]
  apply congrArg₂ List.append
  · rw [←List.map_coe_finRange g.edges.length,List.map_map]
    rfl
  · have hl:=congrArg List.length (internalEdgeList_map g hg o hr)
    simp only [List.length_map] at hl
    simp only [typedWeight,Function.comp_def,Sum.elim_inr,List.map_const',hl]

 theorem weights_get {K : Type} [Zero K] [One K] (x : List K) (e : ExpansionEdge o) :
    (weights g rows x).getD ((incidenceEquiv g hg o hr).edge e).val 0=typedWeight g hg o x e := by
  rw [incidenceEquiv_edge_val,weights_eq_map g hg o hr]
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
    getD_map_idxOf (edgeList g hg o) (typedWeight g hg o x) e (edgeList_mem g hg o e) 0

 theorem evenSubgraphSum_weights {K : Type} [Semiring K] (φ : K→+*ℝ) (x : List K) :
    ((code g rows).toMultiGraph (valid g hg o hr)).evenSubgraphSum
      (fun e=>φ ((weights g rows x).getD e.val 0))=
        (4:ℝ)^g.vertices*(g.toMultiGraph hg).evenSubgraphSum (fun e=>φ (x.getD e.val 0)) := by
  rw [(incidenceEquiv g hg o hr).evenSubgraphSum]
  have hw : ((fun e=>φ ((weights g rows x).getD e.val 0)) ∘ (incidenceEquiv g hg o hr).edge)=
      expansionWeight o (fun e=>φ (x.getD e.val 0)) := by
    funext e
    rw [Function.comp_apply,weights_get]
    cases e <;> simp [typedWeight,expansionWeight]
  rw [hw,expansion_evenSubgraphSum]
  simp

end PlanarHom.FisherExpansionCode
