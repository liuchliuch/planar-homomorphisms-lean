import PlanarHom.FisherCubicReferenceMatching
import PlanarHom.FisherCubicRowFormula
import PlanarHom.PlanarityRowFacePermutation

/-! NEW actual numeric triangle occurrence and canonical port indices for
transporting the inherited cyclic row order. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
local instance (priority := high) cubicRowsEdgeBEq : BEq (Fin g.edges.length⊕(Fin g.vertices×Fin 3)) := instBEqOfDecidableEq

 theorem incidenceEquiv_internal_val (q : Fin g.vertices×Fin 3) :
    ((incidenceEquiv g hg hc).edge (Sum.inr q)).val=g.edges.length+3*q.1.val+q.2.val := by
  rw [incidenceEquiv_edge_val]
  have hm:Sum.inr q∉(List.finRange g.edges.length).map (Sum.inl : Fin g.edges.length→Fin g.edges.length⊕(Fin g.vertices×Fin 3)):=by simp
  rw [edgeList,List.idxOf_append,if_neg hm,List.length_map,List.length_finRange]
  have hh:=idxOf_map_injective (Sum.inr : (Fin g.vertices×Fin 3)→Fin g.edges.length⊕(Fin g.vertices×Fin 3))
    Sum.inr_injective (vertexList g) q
  have hi:(List.map (Sum.inr : (Fin g.vertices×Fin 3)→Fin g.edges.length⊕(Fin g.vertices×Fin 3)) (vertexList g)).idxOf (Sum.inr q)=3*q.1.val+q.2.val:=by
    calc
      _ = (vertexList g).idxOf q := by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using hh
      _ = _ := vertexList_index g q
  rw [hi]
  omega

 theorem row_index_ports (q : Fin g.vertices×Fin 3) :
    (row g q.1.val).idxOf (eraseDart (ports g hg hc q))=q.2.val := by
  let j:Fin ((ordering g hg).degree q.1):=Fin.cast ((ordering g hg).degree_eq q.1 |>.trans (hc q.1)).symm q.2
  have hp:ports g hg hc q=(ordering g hg).darts ⟨q.1,j⟩:=rfl
  have hi:=(ordering_realizes g hg).index_darts g hg q.1 j
  have hrow:FisherExpansionCode.row ((List.range g.vertices).map (row g)) q.1.val=row g q.1.val:=by
    simp [FisherExpansionCode.row,List.getD_eq_getElem?_getD,q.1.isLt]
  rw [hrow,←hp] at hi
  exact hi

 theorem row_index_of_host (a : Fin g.edges.length×Bool) (v : Fin g.vertices)
    (hv : (g.toMultiGraph hg).dartVertex a=v) :
    (row g v.val).idxOf (eraseDart a)=((ports g hg hc).symm a).2.val := by
  have hi:=row_index_ports g hg hc ((ports g hg hc).symm a)
  simpa only [Equiv.apply_symm_apply,ports_vertex g hg hc,hv] using hi

end PlanarHom.FisherCubicCode
