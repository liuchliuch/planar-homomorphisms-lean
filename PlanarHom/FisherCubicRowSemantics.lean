import PlanarHom.FisherCubicRowAddresses
import PlanarHom.FisherExpansionRowSemantics

/-! NEW equality of the computed triangle rows with the inherited typed
rotation under the canonical occurrence scan port permutation. -/
noncomputable section
open Classical
namespace PlanarHom.FisherInheritedRowCode
open Complexity MultiGraph MultiGraph.Kasteleyn Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
variable (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hr : PlanarityRowFaceCode.Realizes g hg rows R)

include hr in
 theorem rowNext_erase (a : Dart (Fin g.edges.length)) :
    PlanarityLRDirect.rowNext (rows.getD ((g.toMultiGraph hg).dartPair a).1.val []) (eraseDart a)=eraseDart (R.rotation a) := by
  have hh:=PlanarityRowFaceCode.rotation_erase g hg rows R hr a
  rw [PlanarityRowFaceCode.rotation,eraseDart_host g hg] at hh
  exact hh.symm

include hr in
 theorem rowPrev_erase (a : Dart (Fin g.edges.length)) :
    PlanarityLRDirect.rowNext (rows.getD ((g.toMultiGraph hg).dartPair a).1.val []).reverse (eraseDart a)=eraseDart (R.rotation.symm a) := by
  rw [hr ((g.toMultiGraph hg).dartPair a).1,←List.map_reverse]
  rw [rowNext_eq_formPerm _ ((List.nodup_reverse.mpr (R.nodup _)).map (eraseDart_injective g)) _
    (List.mem_map.mpr ⟨a,List.mem_reverse.mpr ((R.mem _ _).mpr rfl),rfl⟩)]
  rw [map_formPerm_apply eraseDart (eraseDart_injective g) _ (List.nodup_reverse.mpr (R.nodup _))
    (List.mem_reverse.mpr ((R.mem _ _).mpr rfl)),List.formPerm_reverse]
  rfl

 def typedCubicRows : RotationRows ((FisherCubicCode.code g).toMultiGraph (FisherCubicCode.valid g hg hc)) :=
  (FisherCubicCode.incidenceEquiv g hg hc).dartRelabel.rows (RotationRows.redecidable (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R))

 def erasedCubicDart (a : Dart (Fin g.edges.length⊕(Fin g.vertices×Fin 3))) : PlanarityRotationCode.Dart :=
  (((FisherCubicCode.incidenceEquiv g hg hc).edge a.1).val,a.2)

include hr in
 theorem cubicRow_eq (q : Fin g.vertices×Fin 3) :
    cubicRow g rows ((FisherCubicCode.incidenceEquiv g hg hc).vertex q).val=
      ((RotationRows.redecidable (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R)).row q).map (erasedCubicDart g hg hc) := by
  let p:=FisherCubicCode.ports g hg hc
  let a:=reversePerm _ (p q)
  have ha:((g.toMultiGraph hg).dartPair a).1=q.1:=by
    rw [←dartVertex_reverse]
    change (g.toMultiGraph hg).dartVertex (reversePerm _ (reversePerm _ (p q)))=q.1
    simp only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta]
    have hp:=FisherCubicCode.ports_vertex g hg hc (p q)
    simpa only [p,Equiv.symm_apply_apply] using hp.symm
  have hn:(g.toMultiGraph hg).dartVertex (reversePerm _ (R.rotation a))=q.1:=by
    rw [dartVertex_reverse,R.rotation_host,ha]
  have hp:(g.toMultiGraph hg).dartVertex (reversePerm _ (R.rotation.symm a))=q.1:=by
    rw [dartVertex_reverse]
    exact (R.prev_host a).trans ha
  have hnext:=rowNext_erase g hg rows R hr a
  have hprev:=rowPrev_erase g hg rows R hr a
  rw [ha] at hnext hprev
  have hj:=FisherCubicCode.row_index_of_host g hg hc (reversePerm _ (R.rotation a)) q.1 hn
  have hk:=FisherCubicCode.row_index_of_host g hg hc (reversePerm _ (R.rotation.symm a)) q.1 hp
  let j:Fin 3:=(p.symm (reversePerm _ (R.rotation a))).2
  let k:Fin 3:=(p.symm (reversePerm _ (R.rotation.symm a))).2
  have hJ:(FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
      (PlanarityLRDirect.rowNext (rows.getD q.1.val []) (eraseDart a)))=j.val := by
    rw [hnext]
    exact hj
  have hK:(FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
      (PlanarityLRDirect.rowNext (rows.getD q.1.val []).reverse (eraseDart a)))=k.val := by
    rw [hprev]
    exact hk
  rw [RotationRows.redecidable_row,Fisher.cubicInheritedRows_row]
  rw [cubicRow,FisherCubicCode.incidenceEquiv_vertex_val]
  have hdiv:(3*q.1.val+q.2.val)/3=q.1.val:=by omega
  have hmod:(3*q.1.val+q.2.val)%3=q.2.val:=by omega
  simp only [hdiv,hmod,FisherCubicCode.row_get_ports g hg hc]
  change [eraseDart a,
    (g.edges.length+3*q.1.val+(FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
      (PlanarityLRDirect.rowNext (rows.getD q.1.val []).reverse (eraseDart a))),
      decide (FisherCubicCode.triangleSrc ((FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
        (PlanarityLRDirect.rowNext (rows.getD q.1.val []).reverse (eraseDart a))))=q.2.val)),
    (g.edges.length+3*q.1.val+(FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
      (PlanarityLRDirect.rowNext (rows.getD q.1.val []) (eraseDart a))),
      decide (FisherCubicCode.triangleSrc ((FisherCubicCode.row g q.1.val).idxOf (PlanarityRotationCode.reverse
        (PlanarityLRDirect.rowNext (rows.getD q.1.val []) (eraseDart a))))=q.2.val))]=
    [(Sum.inl a.1,a.2),(Sum.inr (q.1,k),decide (triangle.src k=q.2)),
      (Sum.inr (q.1,j),decide (triangle.src j=q.2))].map (erasedCubicDart g hg hc)
  rw [hJ,hK]
  have he:((FisherCubicCode.incidenceEquiv g hg hc).edge (Sum.inl a.1)).val=a.1.val:=
    FisherCubicCode.referenceEdge_val g hg hc a.1
  simp only [List.map_cons,List.map_nil,erasedCubicDart,FisherCubicCode.incidenceEquiv_internal_val,
    he,eraseDart,Fin.ext_iff,FisherCubicCode.triangleSrc_eq]


include hr in
 theorem cubicRows_realizes : PlanarityRowFaceCode.Realizes (FisherCubicCode.code g)
    (FisherCubicCode.valid g hg hc)
    ((List.range (FisherCubicCode.code g).vertices).map (cubicRow g rows))
    (typedCubicRows g hg hc R) := by
  intro w
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range w.isLt,Option.map_some,Option.getD_some]
  let i:=FisherCubicCode.incidenceEquiv g hg hc
  obtain ⟨q,rfl⟩:=i.vertex.surjective w
  have hh:=cubicRow_eq g hg hc rows R hr q
  change cubicRow g rows (i.vertex q).val=
    (((RotationRows.redecidable (Fisher.cubicInheritedRows (FisherCubicCode.ports g hg hc) R)).row
      (i.vertex.symm (i.vertex q))).map (fun a=>(i.edge a.1,a.2))).map eraseDart
  rw [Equiv.symm_apply_apply,List.map_map]
  exact hh

end PlanarHom.FisherInheritedRowCode
