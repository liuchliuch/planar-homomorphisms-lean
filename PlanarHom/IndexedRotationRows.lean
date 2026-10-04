import PlanarHom.RotationRowsFromPermutation
import PlanarHom.IndexedRotationEuler

/-! NEW table-to-row adapter with the exact reversal convention. A numeric
exterior gap is converted to the incoming predecessor face marker at its host. -/
noncomputable section
open Classical
namespace PlanarHom.IndexedRotationCertificate
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles RadialPotts.Assembly
variable {n m : ℕ} (host : Fin (2*m)→Fin n) (P : Equiv.Perm (Fin (2*m)))
variable (C : LabelCertificate (P*flip m) (Fin n)) (hc : C.label=host)

 def rows : RotationRows (graph host) :=
  RotationRows.ofEndpointPermutation (rotation P) (rotation_cycles host P C hc) (graph_host_surjective host P C hc)

 def faceIndex (m : ℕ) : Dart (Fin m)≃Fin (2*m) := (reversePerm (Fin m)).trans (dartIndexEquiv m)

 theorem rows_face_step (a : Dart (Fin m)) :
    faceIndex m ((rows host P C hc).facePerm a)=P (faceIndex m a) := by
  change dartIndexEquiv m (reversePerm (Fin m) ((rows host P C hc).facePerm a))=_
  rw [rows,RotationRows.ofEndpointPermutation_face_reverse]
  exact face_step P (reversePerm (Fin m) a)

 theorem rows_face_count : count (rows host P C hc).facePerm=count P :=
  count_semiconj _ _ (faceIndex m) (rows_face_step host P C hc)

 theorem rows_euler (he : n+count P=m+2) :
    Fintype.card (Fin n)+count (rows host P C hc).facePerm=Fintype.card (Fin m)+2 := by
  rw [rows_face_count,Fintype.card_fin,Fintype.card_fin]
  exact he

 def closingDart (q : Fin (2*m)) : Dart (Fin m) := (dartIndexEquiv m).symm (P.symm q)

 include C hc in
 theorem closingDart_host (q : Fin (2*m)) :
    ((graph host).dartPair (closingDart P q)).1=host q := by
  have hh:=C.step_label (flip m (P.symm q))
  rw [hc] at hh
  simp only [Equiv.Perm.mul_apply,flip_twice,Equiv.apply_symm_apply] at hh
  rw [←dartVertex_reverse (G:=graph host),graph_host]
  have hi : dartIndexEquiv m (reversePerm (Fin m) (closingDart P q))=flip m (P.symm q) := by
    have h:=flip_index m (closingDart P q).1 (closingDart P q).2
    change flip m (dartIndexEquiv m (closingDart P q))=dartIndexEquiv m (reversePerm (Fin m) (closingDart P q)) at h
    rw [closingDart,Equiv.apply_symm_apply] at h
    exact h.symm
  rw [hi]
  exact hh.symm

 theorem closingDart_injective : Function.Injective (closingDart P) :=
  (dartIndexEquiv m).symm.injective.comp P.symm.injective

 theorem closing_marker_index (q : Fin (2*m)) :
    faceIndex m (reversePerm (Fin m) (closingDart P q))=P.symm q := by
  change dartIndexEquiv m (reversePerm (Fin m) (reversePerm (Fin m) (closingDart P q)))=_
  have hr : reversePerm (Fin m) (reversePerm (Fin m) (closingDart P q))=closingDart P q := by
    simp [reversePerm]
  rw [hr,closingDart,Equiv.apply_symm_apply]

 theorem closing_marker_successor (a b : Fin (2*m)) (h : P a=b) :
    (rows host P C hc).facePerm (reversePerm (Fin m) (closingDart P a))=
      reversePerm (Fin m) (closingDart P b) := by
  apply (faceIndex m).injective
  rw [rows_face_step,closing_marker_index,closing_marker_index,Equiv.apply_symm_apply,←h,Equiv.symm_apply_apply]

end PlanarHom.IndexedRotationCertificate
