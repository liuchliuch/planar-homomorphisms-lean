import PlanarHom.IndexedRotationRows
import PlanarHom.RotationCutEnding
import PlanarHom.ListRotationFilterTransport

/-! NEW literal row comparison: finite numeric rotations and the reconstructed
rows have the same cyclic word, and cutting at one specified dart is unique. -/
noncomputable section
open Classical
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization

theorem rotate_after_eq_of_formPerm_eq {D : Type} [DecidableEq D]
    (xs ys : List D) (a : D) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀b,b∈xs↔b∈ys) (hp : xs.formPerm=ys.formPerm) (ha : a∈xs) :
    xs.rotate (xs.idxOf a+1)=ys.rotate (ys.idxOf a+1) := by
  obtain ⟨pre,hpre⟩:=rotate_after_idxOf_ending xs a hx ha
  obtain ⟨post,hpost⟩:=rotate_after_idxOf_ending ys a hy ((hm a).mp ha)
  have hx' : (pre++[a]).Nodup := hpre ▸ List.nodup_rotate.mpr hx
  have hy' : (post++[a]).Nodup := hpost ▸ List.nodup_rotate.mpr hy
  rw [hpre,hpost]
  apply ending_words_eq pre post a hx' hy'
  · intro b
    rw [←hpre,←hpost,List.mem_rotate,List.mem_rotate]
    exact hm b
  · rw [←hpre,←hpost,List.formPerm_rotate xs hx,List.formPerm_rotate ys hy,hp]

namespace IndexedRotationCertificate
open FinitePermutationCycles RadialPotts.Assembly
variable {n m : ℕ} (host : Fin (2*m)→Fin n) (P : Equiv.Perm (Fin (2*m)))
variable (C : LabelCertificate (P*flip m) (Fin n)) (hc : C.label=host)

theorem rows_host_index (a : Dart (Fin m)) :
    ((graph host).dartPair a).1=host (faceIndex m a) := by
  rw [←dartVertex_reverse (G:=graph host),graph_host]
  rfl

theorem rows_rotation_index (a : Dart (Fin m)) :
    faceIndex m ((rows host P C hc).rotation a)=(P*flip m) (faceIndex m a) := by
  have hh:=rows_face_step host P C hc (reversePerm (Fin m) a)
  have hr : reversePerm (Fin m) (reversePerm (Fin m) a)=a := by simp [reversePerm]
  change faceIndex m ((rows host P C hc).rotation (reversePerm (Fin m) (reversePerm (Fin m) a)))=_ at hh
  rw [hr] at hh
  rw [hh,Equiv.Perm.mul_apply]
  congr 1
  change dartIndexEquiv m (reversePerm (Fin m) (reversePerm (Fin m) a))=flip m (dartIndexEquiv m (reversePerm (Fin m) a))
  rw [hr]
  exact (flip_index m (reversePerm (Fin m) a).1 (reversePerm (Fin m) a).2).trans (by congr 1) |>.symm

def mappedRow (nr : Fin n→List (Fin (2*m))) (v : Fin n) : List (Dart (Fin m)) :=
  (nr v).map (faceIndex m).symm

variable (nr : Fin n→List (Fin (2*m)))
variable (hn : ∀v,(nr v).Nodup) (hm : ∀v a,a∈nr v↔host a=v)
variable (hs : ∀a,(nr (host a)).formPerm a=(P*flip m) a)

include hm in
theorem mappedRow_mem (v : Fin n) (a : Dart (Fin m)) :
    a∈mappedRow nr v ↔ ((graph host).dartPair a).1=v := by
  rw [mappedRow,List.mem_map]
  constructor
  · rintro ⟨b,hb,rfl⟩
    rw [rows_host_index,Equiv.apply_symm_apply]
    exact (hm v b).mp hb
  · intro ha
    refine ⟨faceIndex m a,?_,Equiv.symm_apply_apply _ _⟩
    exact (hm v _).mpr ((rows_host_index host a).symm.trans ha)

include hn in
theorem mappedRow_nodup (v : Fin n) : (mappedRow nr v).Nodup :=
  (hn v).map (faceIndex m).symm.injective

include hm hs in
theorem mappedRow_formPerm (v : Fin n) :
    ((rows host P C hc).row v).formPerm=(mappedRow nr v).formPerm := by
  apply Equiv.ext
  intro a
  by_cases ha : ((graph host).dartPair a).1=v
  · have hleft : ((rows host P C hc).row v).formPerm a=(rows host P C hc).rotation a := by
      rw [RotationRows.rotation_apply,ha]
    rw [hleft]
    apply (faceIndex m).injective
    rw [rows_rotation_index]
    have hmap:=ListRotationErasure.formPerm_map_apply (faceIndex m).symm (faceIndex m).symm.injective (nr v) (faceIndex m a)
    simp only [Equiv.symm_apply_apply] at hmap
    change _=faceIndex m ((List.map (faceIndex m).symm (nr v)).formPerm a)
    rw [hmap,Equiv.apply_symm_apply]
    have hh : host (faceIndex m a)=v := (rows_host_index host a).symm.trans ha
    exact (hh ▸ hs (faceIndex m a)).symm
  · have hleft : a∉(rows host P C hc).row v := by rw [(rows host P C hc).mem]; exact ha
    have hright : a∉mappedRow nr v := by rw [mappedRow_mem host nr hm]; exact ha
    rw [List.formPerm_apply_of_not_mem hleft,List.formPerm_apply_of_not_mem hright]

include hm hs hn in
theorem rows_cut_eq_mapped_rotate (v : Fin n) (a : Dart (Fin m)) (k : ℕ)
    (ha : ((graph host).dartPair a).1=v)
    (hend : ((mappedRow nr v).rotate k).getLast?=some a) :
    ((rows host P C hc).row v).rotate (((rows host P C hc).row v).idxOf a+1)=
      (mappedRow nr v).rotate k := by
  obtain ⟨pre,hpre⟩:=rotate_after_idxOf_ending ((rows host P C hc).row v) a
    ((rows host P C hc).nodup v) (((rows host P C hc).mem v a).mpr ha)
  obtain ⟨post,hpost⟩:=List.getLast?_eq_some_iff.mp hend
  have hx : (pre++[a]).Nodup := hpre ▸ List.nodup_rotate.mpr ((rows host P C hc).nodup v)
  have hy : (post++[a]).Nodup := hpost ▸ List.nodup_rotate.mpr (mappedRow_nodup nr hn v)
  rw [hpre,hpost]
  apply ending_words_eq pre post a hx hy
  · intro b
    rw [←hpre,←hpost,List.mem_rotate,List.mem_rotate,(rows host P C hc).mem,mappedRow_mem host nr hm]
  · rw [←hpre,←hpost,List.formPerm_rotate _ ((rows host P C hc).nodup v),
      List.formPerm_rotate _ (mappedRow_nodup nr hn v)]
    exact mappedRow_formPerm host P C hc nr hm hs v

end IndexedRotationCertificate
end PlanarHom
