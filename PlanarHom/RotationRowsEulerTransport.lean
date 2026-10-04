import PlanarHom.RotationRowsTransport
import PlanarHom.ColoringIncidenceComponents
import PlanarHom.RotationFaceCycleDuality
import PlanarHom.FinitePermutationCycleTransport

noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn FinitePermutationCycles
variable {V E W F : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]
variable {G : MultiGraph V E} {H : MultiGraph W F}

theorem transport_rotation_step (R : RotationRows G) (i : IncidenceEquiv G H) (a : Dart E) :
    (R.transport i).rotation (i.darts a)=i.darts (R.rotation a) := by
  change (((R.transport i).row (H.dartPair (i.darts a)).1).formPerm (i.darts a))=_
  rw [i.dart_host]
  change ((R.row (i.vertex.symm (i.vertex (G.dartPair a).1))).map i.darts).formPerm (i.darts a)=_
  rw [i.vertex.symm_apply_apply]
  exact map_formPerm_apply i.darts i.darts.injective _ (R.nodup _) ((R.mem _ _).mpr rfl)

theorem transport_face_step (R : RotationRows G) (i : IncidenceEquiv G H) (a : Dart E) :
    (R.transport i).facePerm (i.darts a)=i.darts (R.facePerm a) := by
  change (R.transport i).rotation (reversePerm F (i.darts a))=i.darts (R.rotation (reversePerm E a))
  have hr : reversePerm F (i.darts a)=i.darts (reversePerm E a) := by obtain ⟨e,b⟩:=a; cases b <;> rfl
  rw [hr,transport_rotation_step]

theorem transport_face_count (R : RotationRows G) (i : IncidenceEquiv G H) :
    count (R.transport i).facePerm=count R.facePerm :=
  (count_of_step R.facePerm (R.transport i).facePerm i.darts (fun a=>(transport_face_step R i a).symm)).symm

theorem transport_euler (R : RotationRows G) (i : IncidenceEquiv G H)
    (h : Fintype.card V+count R.facePerm=Fintype.card E+2*G.componentCount Finset.univ) :
    Fintype.card W+count (R.transport i).facePerm=Fintype.card F+2*H.componentCount Finset.univ := by
  rw [transport_face_count,i.componentCount_eq,←Fintype.card_congr i.vertex,←Fintype.card_congr i.edge]
  exact h

end PlanarHom.PlanarityLRRealization.RotationRows
