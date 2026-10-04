import PlanarHom.FisherInheritedRowProgram
import PlanarHom.FisherExpansionWeightSemantics
import PlanarHom.FisherNumericRotationTransport
import PlanarHom.FisherExpansionRotation

/-! NEW exact serialized path/loop dart addresses used by inherited rows. -/
noncomputable section
open Classical
namespace PlanarHom.FisherExpansionCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)
variable {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)
local instance (priority := high) expansionRowsEdgeBEq : BEq (ExpansionEdge o) := instBEqOfDecidableEq
local instance (priority := high) expansionRowsInternalBEq : BEq (ExpansionInternalEdge o) := instBEqOfDecidableEq

 def internalSlot (e : ExpansionInternalEdge o) : ℕ×ℕ :=
  (e.1.val,Sum.elim Fin.val (fun b=>if b then o.degree e.1+2 else o.degree e.1+1) e.2)

 theorem internalSlot_injective : Function.Injective (internalSlot g hg o) := by
  rintro ⟨v,e⟩ ⟨w,f⟩ h
  have hv:v=w:=Fin.ext (congrArg Prod.fst h)
  subst w
  have hi:=congrArg Prod.snd h
  dsimp only [internalSlot] at hi
  apply congrArg (Sigma.mk v)
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Fin.ext hi)
    | inr b =>
      cases b
      · simp only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,if_false] at hi
        have hbound:=e.isLt
        rw [hi] at hbound
        exact (Nat.lt_irrefl _ hbound).elim
      · simp only [Sum.elim_inl,Sum.elim_inr,if_true] at hi
        have hbound:=e.isLt
        rw [hi] at hbound
        exact (Nat.not_lt_of_ge (Nat.le_succ _) hbound).elim
  | inr b =>
    cases f with
    | inl f =>
      cases b
      · simp only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,if_false] at hi
        have hbound:=f.isLt
        rw [←hi] at hbound
        exact (Nat.lt_irrefl _ hbound).elim
      · simp only [Sum.elim_inl,Sum.elim_inr,if_true] at hi
        have hbound:=f.isLt
        rw [←hi] at hbound
        exact (Nat.not_lt_of_ge (Nat.le_succ _) hbound).elim
    | inr c => cases b <;> cases c <;> simp_all

 include hr in
 theorem internalEdgeList_slots :
    (internalEdgeList g hg o).map (internalSlot g hg o)=FisherInheritedRowCode.edgeSlots g rows := by
  simp only [internalEdgeList,sigmaList,List.map_flatMap,List.map_map,Function.comp_def]
  unfold FisherInheritedRowCode.edgeSlots
  rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
  congr 1
  funext v
  rw [←hr.degree_eq g hg v]
  simp only [localEdgeList,List.map_append,List.map_map,List.map_cons,List.map_nil,internalSlot,
    Function.comp_def,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,if_false,if_true]
  rw [show o.degree v+3=(o.degree v+1)+1+1 by omega,List.range_succ,List.range_succ,List.map_append,List.map_append]
  rw [←List.map_coe_finRange (o.degree v+1),List.map_map]
  simp only [List.map_singleton,List.append_assoc,List.singleton_append]
  rfl

 theorem incidenceEquiv_external_val (e : Fin g.edges.length) :
    ((incidenceEquiv g hg o hr).edge (Sum.inl e)).val=e.val := by
  rw [incidenceEquiv_edge_val]
  have hm:Sum.inl e∈(List.finRange g.edges.length).map (Sum.inl : Fin g.edges.length→ExpansionEdge o):=
    List.mem_map.mpr ⟨e,List.mem_finRange _,rfl⟩
  rw [edgeList,List.idxOf_append,if_pos hm]
  calc
    _ = (List.finRange g.edges.length).idxOf e := by
      simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using idxOf_map_injective
        (Sum.inl : Fin g.edges.length→ExpansionEdge o) Sum.inl_injective (List.finRange g.edges.length) e
    _ = e.val := List.idxOf_finRange e

 theorem incidenceEquiv_internal_val (e : ExpansionInternalEdge o) :
    ((incidenceEquiv g hg o hr).edge (Sum.inr e)).val=
      FisherInheritedRowCode.internalNumber g rows (internalSlot g hg o e).1 (internalSlot g hg o e).2 := by
  rw [incidenceEquiv_edge_val]
  have hm:Sum.inr e∉(List.finRange g.edges.length).map (Sum.inl : Fin g.edges.length→ExpansionEdge o):=by simp
  rw [edgeList,List.idxOf_append,if_neg hm,List.length_map,List.length_finRange]
  unfold FisherInheritedRowCode.internalNumber
  rw [←internalEdgeList_slots g hg o hr]
  have h₁:=idxOf_map_injective (Sum.inr : ExpansionInternalEdge o→ExpansionEdge o)
    Sum.inr_injective (internalEdgeList g hg o) e
  have h₂:=idxOf_map_injective (internalSlot g hg o) (internalSlot_injective g hg o) (internalEdgeList g hg o) e
  simp only [List.idxOf,Lean.Grind.beq_eq_decide_eq] at h₁ h₂ ⊢
  rw [h₁,h₂,Nat.add_comm]

 theorem incidenceEquiv_vertex_val (v : ExpansionVertex o) :
    ((incidenceEquiv g hg o hr).vertex v).val=vertexNumber g rows v.1.val v.2.val := by
  change ((codeIncidenceEquiv (enumeratedCode_eq g hg o hr) _ _).vertex
    ((enumeratedIncidenceEquiv _ _ _ _ _ _ _).vertex v)).val=_
  rw [codeIncidenceEquiv_vertex_val,vertexNumber_eq g hg o hr]
  simp [enumeratedIncidenceEquiv,List.Nodup.getEquivOfForallMemList,List.idxOf,Lean.Grind.beq_eq_decide_eq]
  rfl

end PlanarHom.FisherExpansionCode
