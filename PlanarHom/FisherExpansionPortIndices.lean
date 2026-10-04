import PlanarHom.FisherExpansionEnumeration

/-! NEW exact port-position identities for the emitted expansion addresses. -/
noncomputable section
open Classical
namespace PlanarHom.FisherContourOrder
open Complexity MultiGraph Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable {rows : Rows} {o : (g.toMultiGraph hg).IncidenceOrdering}

 theorem Realizes.index_darts (hr : Realizes g hg rows o) (v : Fin g.vertices) (i : Fin (o.degree v)) :
    (FisherExpansionCode.row rows v.val).idxOf (eraseDart (o.darts ⟨v,i⟩))=i.val := by
  rw [hr v]
  have hinj : Function.Injective (fun j:Fin (o.degree v)=>eraseDart (o.darts ⟨v,j⟩)) := by
    intro j k h
    have he:=o.darts.injective (eraseDart_injective g h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  rw [List.map_ofFn]
  have hh:=List.idxOf_getElem (List.nodup_ofFn.mpr hinj) i.val (by simpa using i.isLt)
  simpa only [List.getElem_ofFn,Function.comp_apply,List.idxOf,Lean.Grind.beq_eq_decide_eq] using hh

 theorem endpoint_erase (a : Fin g.edges.length×Bool) :
    FisherExpansionCode.endpoint g (eraseDart a)=((g.toMultiGraph hg).dartVertex a).val := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [FisherExpansionCode.endpoint,eraseDart,dartVertex,MixedCode.toMultiGraph,
    List.getD_eq_getElem?_getD,e.isLt,List.get_eq_getElem]

 theorem Realizes.portNumber_darts (hr : Realizes g hg rows o) (v : Fin g.vertices) (i : Fin (o.degree v)) :
    FisherExpansionCode.portNumber g rows (eraseDart (o.darts ⟨v,i⟩))=
      FisherExpansionCode.vertexNumber g rows v.val (i.val+1) := by
  have hv:=congrArg Fin.val (o.darts_vertex ⟨v,i⟩)
  rw [FisherExpansionCode.portNumber,endpoint_erase g hg,hv,hr.index_darts g hg v i]

end PlanarHom.FisherContourOrder

namespace PlanarHom.FisherExpansionCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)

 theorem portNumber_eq {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)
    (a : Fin g.edges.length×Bool) :
    portNumber g rows (eraseDart a)=(vertexList g hg o).idxOf (portVertex o (o.darts.symm a)) := by
  let q:=o.darts.symm a
  have ha:o.darts q=a:=o.darts.apply_symm_apply a
  rw [←ha,hr.portNumber_darts g hg q.1 q.2]
  simpa only [Equiv.symm_apply_apply] using vertexNumber_eq g hg o hr (portVertex o q)

end PlanarHom.FisherExpansionCode
