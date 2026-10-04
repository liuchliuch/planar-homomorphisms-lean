import PlanarHom.FisherCubicOrdering
import PlanarHom.FisherExpansionPortIndices

/-! NEW equality of the canonical scan port addresses with their typed
three-port equivalence, retaining endpoint directions. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)

 theorem portNumber_ports (q : Fin g.vertices×Fin 3) :
    portNumber g (eraseDart (ports g hg hc q))=3*q.1.val+q.2.val := by
  let j:Fin ((ordering g hg).degree q.1):=Fin.cast ((ordering g hg).degree_eq q.1 |>.trans (hc q.1)).symm q.2
  have hp:ports g hg hc q=(ordering g hg).darts ⟨q.1,j⟩:=rfl
  have hv:((g.toMultiGraph hg).dartVertex (ports g hg hc q))=q.1:=by
    rw [hp]
    exact (ordering g hg).darts_vertex _
  have hi:=(ordering_realizes g hg).index_darts g hg q.1 j
  have hrow:FisherExpansionCode.row ((List.range g.vertices).map (row g)) q.1.val=row g q.1.val:=by
    simp [FisherExpansionCode.row,List.getD_eq_getElem?_getD,q.1.isLt]
  rw [hrow,←hp] at hi
  rw [portNumber,FisherContourOrder.endpoint_erase g hg,hv,hi]
  rfl

 theorem row_get_ports (v : Fin g.vertices) (i : Fin 3) :
    (row g v.val).getD i.val (0,false)=eraseDart (ports g hg hc (v,i)) := by
  let j:Fin ((ordering g hg).degree v):=Fin.cast ((ordering g hg).degree_eq v |>.trans (hc v)).symm i
  have hp:ports g hg hc (v,i)=(ordering g hg).darts ⟨v,j⟩:=rfl
  have hi:=(ordering_realizes g hg).index_darts g hg v j
  have hrow:FisherExpansionCode.row ((List.range g.vertices).map (row g)) v.val=row g v.val:=by
    simp [FisherExpansionCode.row,List.getD_eq_getElem?_getD,v.isLt]
  rw [hrow,←hp] at hi
  change (row g v.val).idxOf (eraseDart (ports g hg hc (v,i)))=i.val at hi
  have hn:(row g v.val).length=3:=((ordering_degree g hg v).symm.trans ((ordering g hg).degree_eq v)).trans (hc v)
  have hlt:i.val<(row g v.val).length:=by rw [hn]; exact i.isLt
  have hi' : @List.idxOf _ instBEqOfDecidableEq (eraseDart (ports g hg hc (v,i))) (row g v.val)=i.val := by
    simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using hi
  have hget:=List.getElem_idxOf (hi' ▸ hlt)
  simpa [List.getD_eq_getElem?_getD,hlt,hi'] using hget

 theorem portNumber_inverse (a : Fin g.edges.length×Bool) :
    portNumber g (eraseDart a)=3*((ports g hg hc).symm a).1.val+((ports g hg hc).symm a).2.val := by
  have hh:=portNumber_ports g hg hc ((ports g hg hc).symm a)
  simpa only [Equiv.apply_symm_apply] using hh

end PlanarHom.FisherCubicCode
