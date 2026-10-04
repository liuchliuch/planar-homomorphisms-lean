import PlanarHom.FisherExpansionRowAddresses

/-! NEW equality of the actual numeric inherited expansion rows with the
proved typed path/endloop rotation, including isolated original vertices. -/
noncomputable section
open Classical
namespace PlanarHom.FisherInheritedRowCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)
variable {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)

 def erasedExpansionDart (a : MultiGraph.Kasteleyn.Dart (ExpansionEdge o)) : PlanarityRotationCode.Dart :=
  (((FisherExpansionCode.incidenceEquiv g hg o hr).edge a.1).val,a.2)

 theorem vertexSlots_get (q : ExpansionVertex o) :
    (FisherExpansionCode.vertexSlots g rows).getD ((FisherExpansionCode.incidenceEquiv g hg o hr).vertex q).val (0,0)=
      (q.1.val,q.2.val) := by
  rw [FisherExpansionCode.incidenceEquiv_vertex_val]
  have hm:(q.1.val,q.2.val)∈FisherExpansionCode.vertexSlots g rows:=by
    rw [←FisherExpansionCode.vertexList_erase g hg o hr]
    exact List.mem_map.mpr ⟨q,FisherExpansionCode.vertexList_mem g hg o q,rfl⟩
  have hh:=getD_map_idxOf (FisherExpansionCode.vertexSlots g rows) id (q.1.val,q.2.val) hm (0,0)
  simpa only [FisherExpansionCode.vertexNumber,List.map_id,List.idxOf,Lean.Grind.beq_eq_decide_eq] using hh

include hr in
 theorem row_get (v : Fin g.vertices) (i : Fin (o.degree v)) :
    (FisherExpansionCode.row rows v.val).getD i.val (0,false)=eraseDart (o.darts ⟨v,i⟩) := by
  rw [hr v]
  simp [List.getD_eq_getElem?_getD,i.isLt]

 theorem expansionRow_eq (q : ExpansionVertex o) :
    expansionRow g rows ((FisherExpansionCode.incidenceEquiv g hg o hr).vertex q).val=
      (Fisher.expansionRow o q).map (erasedExpansionDart g hg o hr) := by
  rcases q with ⟨v,j⟩
  apply (Fisher.forall_fin_endpoints (d:=o.degree v) (fun j=>
    expansionRow g rows ((FisherExpansionCode.incidenceEquiv g hg o hr).vertex ⟨v,j⟩).val=
      (Fisher.expansionRow o ⟨v,j⟩).map (erasedExpansionDart g hg o hr))).mpr ?_ j
  constructor
  · rw [expansionRow,vertexSlots_get g hg o hr]
    simp [←hr.degree_eq g hg v,Fisher.expansionRow_zero,
      erasedExpansionDart,Fisher.expansionPathDart,Fisher.expansionLoopDart,FisherExpansionCode.incidenceEquiv_internal_val,
      FisherExpansionCode.internalSlot]
  constructor
  · rw [expansionRow,vertexSlots_get g hg o hr]
    simp [←hr.degree_eq g hg v,Fisher.expansionRow_last,
      erasedExpansionDart,Fisher.expansionPathDart,Fisher.expansionLoopDart,FisherExpansionCode.incidenceEquiv_internal_val,
      FisherExpansionCode.internalSlot]
  · intro i
    change expansionRow g rows ((FisherExpansionCode.incidenceEquiv g hg o hr).vertex ⟨v,i.succ.castSucc⟩).val=
      (Fisher.expansionRow o ⟨v,i.succ.castSucc⟩).map (erasedExpansionDart g hg o hr)
    have hi:i.val+1≠o.degree v+1:=by have:=i.isLt; omega
    rw [Fisher.expansionRow_port,expansionRow,vertexSlots_get g hg o hr]
    dsimp only
    simp only [Fin.coe_castSucc,Fin.val_succ]
    rw [←hr.degree_eq g hg v,if_neg (by omega : i.val+1≠0),if_neg hi,Nat.add_sub_cancel,
      row_get g hg o hr v i]
    simp [erasedExpansionDart,Fisher.expansionPathDart,Fisher.expansionPortDart,
      FisherExpansionCode.incidenceEquiv_internal_val,FisherExpansionCode.incidenceEquiv_external_val,
      FisherExpansionCode.internalSlot,PlanarityRotationCode.reverse,eraseDart]

 def typedExpansionRows : RotationRows ((FisherExpansionCode.code g rows).toMultiGraph (FisherExpansionCode.valid g hg o hr)) :=
  (FisherExpansionCode.incidenceEquiv g hg o hr).dartRelabel.rows
    { row:=Fisher.expansionRow o
      nodup:=Fisher.expansionRow_nodup o
      mem:=fun q=>(expansionGraph o).row_mem_of_degree q (Fisher.expansionRow o q)
        (Fisher.expansionRow_nodup o q) (Fisher.expansionRow_hosts o q)
        (by rw [Fisher.expansionRow_length,Fisher.expansion_is_cubic]) }

 theorem typedExpansionRows_eq_redecidable : typedExpansionRows g hg o hr=
    (FisherExpansionCode.incidenceEquiv g hg o hr).dartRelabel.rows
      (RotationRows.redecidable (Fisher.expansionRows o)) := rfl

 theorem expansionRows_realizes : PlanarityRowFaceCode.Realizes (FisherExpansionCode.computed g)
    (FisherExpansionCode.computed_valid g hg) (expansionRows g)
    (typedExpansionRows g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg)) := by
  intro w
  simp only [expansionRows,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range w.isLt,Option.map_some,Option.getD_some]
  let i:=FisherExpansionCode.computedIncidenceEquiv g hg
  obtain ⟨q,rfl⟩:=i.vertex.surjective w
  have hh:=expansionRow_eq g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg) q
  change expansionRow g (FisherContourOrder.computedRows g) (i.vertex q).val=
    ((Fisher.expansionRow (FisherContourOrder.ordering g hg) (i.vertex.symm (i.vertex q))).map
      (fun a=>(i.edge a.1,a.2))).map eraseDart
  rw [Equiv.symm_apply_apply,List.map_map]
  exact hh


end PlanarHom.FisherInheritedRowCode
