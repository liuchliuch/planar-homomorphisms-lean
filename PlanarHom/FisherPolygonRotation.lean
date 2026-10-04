import PlanarHom.FisherRotationOrdering
import PlanarHom.RotationFaceCycleDuality

/-! NEW literal polygon replacement of cyclic vertices. On a cubic graph the
polygon is a triangle. Every new vertex is an original outward dart. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
variable (R : RotationRows G)

 def polygonGraph : MultiGraph (Dart E) (E ⊕ Dart E) where
  src := Sum.elim (fun e=>(e,true)) id
  dst := Sum.elim (fun e=>(e,false)) R.rotation

 def polygonExternal (a : Dart E) : Dart (E ⊕ Dart E) := (.inl a.1,a.2)
 def polygonOutgoing (a : Dart E) : Dart (E ⊕ Dart E) := (.inr a,true)
 def polygonIncoming (a : Dart E) : Dart (E ⊕ Dart E) := (.inr (R.rotation.symm a),false)

 def polygonRow (a : Dart E) : List (Dart (E ⊕ Dart E)) :=
  [polygonExternal a,polygonOutgoing a,polygonIncoming R a]

 theorem polygonRow_nodup (a : Dart E) : (polygonRow R a).Nodup := by
  simp [polygonRow,polygonExternal,polygonOutgoing,polygonIncoming]

 theorem mem_polygonRow (a : Dart E) (d : Dart (E ⊕ Dart E)) :
    d∈polygonRow R a ↔ ((polygonGraph R).dartPair d).1=a := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e =>
      rcases a with ⟨f,c⟩
      cases b <;> cases c <;> simp [polygonRow,polygonExternal,polygonOutgoing,polygonIncoming,polygonGraph,dartPair,eq_comm]
  | inr e =>
      cases b
      · simp only [polygonRow,polygonExternal,polygonOutgoing,polygonIncoming,List.mem_cons,
          List.not_mem_nil,or_false,Prod.mk.injEq,Sum.inr_ne_inl,Sum.inr.injEq,Bool.false_ne_true,
          Bool.false_eq_true,false_and,and_false,false_or,and_true,polygonGraph,dartPair,if_false,
          Sum.elim_inr]
        exact R.rotation.eq_symm_apply
      · simp only [polygonRow,polygonExternal,polygonOutgoing,polygonIncoming,List.mem_cons,
          List.not_mem_nil,or_false,Prod.mk.injEq,Sum.inr_ne_inl,Sum.inr.injEq,Bool.true_eq_false,
          false_and,and_false,false_or,and_true,or_false,polygonGraph,dartPair,if_true,Sum.elim_inr,id_eq]

 def polygonRows : RotationRows (polygonGraph R) where
  row := polygonRow R
  nodup := polygonRow_nodup R
  mem := mem_polygonRow R

 theorem polygonExternal_host (a : Dart E) :
    ((polygonGraph R).dartPair (polygonExternal a)).1=a := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

 theorem polygonOutgoing_host (a : Dart E) :
    ((polygonGraph R).dartPair (polygonOutgoing a)).1=a := rfl

 theorem polygonIncoming_host (a : Dart E) :
    ((polygonGraph R).dartPair (polygonIncoming R a)).1=a := R.rotation.apply_symm_apply a

 theorem polygonRotation_external (a : Dart E) :
    (polygonRows R).rotation (polygonExternal a)=polygonOutgoing a := by
  rw [RotationRows.rotation_apply,polygonExternal_host]
  have h := List.formPerm_apply_getElem (polygonRow R a) (polygonRow_nodup R a) 0 (by simp [polygonRow])
  simpa [polygonRows,polygonRow] using h

 theorem polygonRotation_outgoing (a : Dart E) :
    (polygonRows R).rotation (polygonOutgoing a)=polygonIncoming R a := by
  rw [RotationRows.rotation_apply,polygonOutgoing_host]
  have h := List.formPerm_apply_getElem (polygonRow R a) (polygonRow_nodup R a) 1 (by simp [polygonRow])
  simpa [polygonRows,polygonRow] using h

 theorem polygonRotation_incoming (a : Dart E) :
    (polygonRows R).rotation (polygonIncoming R a)=polygonExternal a := by
  rw [RotationRows.rotation_apply,polygonIncoming_host]
  have h := List.formPerm_apply_getElem (polygonRow R a) (polygonRow_nodup R a) 2 (by simp [polygonRow])
  simpa [polygonRows,polygonRow] using h

 theorem polygonFace_external [Fintype V] [Fintype E] (a : Dart E) :
    (polygonRows R).facePerm (polygonExternal a)=polygonOutgoing (reversePerm E a) := by
  change (polygonRows R).rotation (polygonExternal (reversePerm E a))=_
  exact polygonRotation_external R _

 theorem polygonFace_outgoing [Fintype V] [Fintype E] (a : Dart E) :
    (polygonRows R).facePerm (polygonOutgoing a)=polygonExternal (R.rotation a) := by
  have h : reversePerm (E⊕Dart E) (polygonOutgoing a)=polygonIncoming R (R.rotation a) := by
    change ((Sum.inr a : E⊕Dart E),false)=(.inr (R.rotation.symm (R.rotation a)),false)
    rw [R.rotation.symm_apply_apply]
  change (polygonRows R).rotation (reversePerm _ (polygonOutgoing a))=_
  rw [h,polygonRotation_incoming]

 theorem polygonFace_incoming [Fintype V] [Fintype E] (a : Dart E) :
    (polygonRows R).facePerm (.inr a,false)=polygonIncoming R a := by
  change (polygonRows R).rotation (polygonOutgoing a)=_
  exact polygonRotation_outgoing R a

end PlanarHom.Fisher
