import PlanarHom.IndexedRotationRows
import PlanarHom.ColoringFramedMacroPorts

/-! NEW typed cyclic rows for the four actual framed macros. Hosted table
gaps are converted to their proved incoming predecessor markers. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
open Classical
namespace PlanarHom.ColoringMacroFaces
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
namespace TestFramed
 def typedRows : RotationRows framedGraph :=
  IndexedRotationCertificate.rows (n:=118) (m:=285) host permutation rotationCertificate rfl
 def leftClosing (i : Fin 9) : Dart (Fin 285) :=
  IndexedRotationCertificate.closingDart (m:=285) permutation (leftGap i)
 def rightClosing (i : Fin 0) : Dart (Fin 285) :=
  IndexedRotationCertificate.closingDart (m:=285) permutation (rightGap i)
 theorem leftClosing_host (i : Fin 9) : (framedGraph.dartPair (leftClosing i)).1=leftVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=118) (m:=285) host permutation rotationCertificate rfl (leftGap i)).trans (left_host i)
 theorem rightClosing_host (i : Fin 0) : (framedGraph.dartPair (rightClosing i)).1=rightVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=118) (m:=285) host permutation rotationCertificate rfl (rightGap i)).trans (right_host i)
 theorem typedRows_euler : Fintype.card (Fin 118)+count typedRows.facePerm=Fintype.card (Fin 285)+2 :=
  IndexedRotationCertificate.rows_euler (n:=118) (m:=285) host permutation rotationCertificate rfl euler
 theorem leftClosing_injective : Function.Injective leftClosing := by
  intro i j he
  apply left_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (leftClosing_host i).symm.trans (hh.trans (leftClosing_host j))
 theorem rightClosing_injective : Function.Injective rightClosing := by
  intro i j he
  apply right_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (rightClosing_host i).symm.trans (hh.trans (rightClosing_host j))
 theorem leftMarkers_successor (i : Fin 8) :
    typedRows.facePerm (reversePerm _ (leftClosing i.succ))=reversePerm _ (leftClosing i.castSucc) :=
  IndexedRotationCertificate.closing_marker_successor (n:=118) (m:=285) host permutation rotationCertificate rfl _ _ (left_successor i)
end TestFramed
namespace WireFramed
 def typedRows : RotationRows framedGraph :=
  IndexedRotationCertificate.rows (n:=534) (m:=1323) host permutation rotationCertificate rfl
 def leftClosing (i : Fin 3) : Dart (Fin 1323) :=
  IndexedRotationCertificate.closingDart (m:=1323) permutation (leftGap i)
 def rightClosing (i : Fin 3) : Dart (Fin 1323) :=
  IndexedRotationCertificate.closingDart (m:=1323) permutation (rightGap i)
 theorem leftClosing_host (i : Fin 3) : (framedGraph.dartPair (leftClosing i)).1=leftVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=534) (m:=1323) host permutation rotationCertificate rfl (leftGap i)).trans (left_host i)
 theorem rightClosing_host (i : Fin 3) : (framedGraph.dartPair (rightClosing i)).1=rightVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=534) (m:=1323) host permutation rotationCertificate rfl (rightGap i)).trans (right_host i)
 theorem typedRows_euler : Fintype.card (Fin 534)+count typedRows.facePerm=Fintype.card (Fin 1323)+2 :=
  IndexedRotationCertificate.rows_euler (n:=534) (m:=1323) host permutation rotationCertificate rfl euler
 theorem leftClosing_injective : Function.Injective leftClosing := by
  intro i j he
  apply left_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (leftClosing_host i).symm.trans (hh.trans (leftClosing_host j))
 theorem rightClosing_injective : Function.Injective rightClosing := by
  intro i j he
  apply right_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (rightClosing_host i).symm.trans (hh.trans (rightClosing_host j))
 theorem leftMarkers_successor (i : Fin 2) :
    typedRows.facePerm (reversePerm _ (leftClosing i.succ))=reversePerm _ (leftClosing i.castSucc) :=
  IndexedRotationCertificate.closing_marker_successor (n:=534) (m:=1323) host permutation rotationCertificate rfl _ _ (left_successor i)
 theorem rightMarkers_successor (i : Fin 2) :
    typedRows.facePerm (reversePerm _ (rightClosing i.castSucc))=reversePerm _ (rightClosing i.succ) :=
  IndexedRotationCertificate.closing_marker_successor (n:=534) (m:=1323) host permutation rotationCertificate rfl _ _ (right_successor i)
end WireFramed
namespace CrossFramed
 def typedRows : RotationRows framedGraph :=
  IndexedRotationCertificate.rows (n:=1274) (m:=3168) host permutation rotationCertificate rfl
 def leftClosing (i : Fin 6) : Dart (Fin 3168) :=
  IndexedRotationCertificate.closingDart (m:=3168) permutation (leftGap i)
 def rightClosing (i : Fin 6) : Dart (Fin 3168) :=
  IndexedRotationCertificate.closingDart (m:=3168) permutation (rightGap i)
 theorem leftClosing_host (i : Fin 6) : (framedGraph.dartPair (leftClosing i)).1=leftVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=1274) (m:=3168) host permutation rotationCertificate rfl (leftGap i)).trans (left_host i)
 theorem rightClosing_host (i : Fin 6) : (framedGraph.dartPair (rightClosing i)).1=rightVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=1274) (m:=3168) host permutation rotationCertificate rfl (rightGap i)).trans (right_host i)
 theorem typedRows_euler : Fintype.card (Fin 1274)+count typedRows.facePerm=Fintype.card (Fin 3168)+2 :=
  IndexedRotationCertificate.rows_euler (n:=1274) (m:=3168) host permutation rotationCertificate rfl euler
 theorem leftClosing_injective : Function.Injective leftClosing := by
  intro i j he
  apply left_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (leftClosing_host i).symm.trans (hh.trans (leftClosing_host j))
 theorem rightClosing_injective : Function.Injective rightClosing := by
  intro i j he
  apply right_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (rightClosing_host i).symm.trans (hh.trans (rightClosing_host j))
 theorem leftMarkers_successor (i : Fin 5) :
    typedRows.facePerm (reversePerm _ (leftClosing i.succ))=reversePerm _ (leftClosing i.castSucc) :=
  IndexedRotationCertificate.closing_marker_successor (n:=1274) (m:=3168) host permutation rotationCertificate rfl _ _ (left_successor i)
 theorem rightMarkers_successor (i : Fin 5) :
    typedRows.facePerm (reversePerm _ (rightClosing i.castSucc))=reversePerm _ (rightClosing i.succ) :=
  IndexedRotationCertificate.closing_marker_successor (n:=1274) (m:=3168) host permutation rotationCertificate rfl _ _ (right_successor i)
end CrossFramed
namespace FanFramed
 def typedRows : RotationRows framedGraph :=
  IndexedRotationCertificate.rows (n:=1058) (m:=2632) host permutation rotationCertificate rfl
 def leftClosing (i : Fin 3) : Dart (Fin 2632) :=
  IndexedRotationCertificate.closingDart (m:=2632) permutation (leftGap i)
 def rightClosing (i : Fin 6) : Dart (Fin 2632) :=
  IndexedRotationCertificate.closingDart (m:=2632) permutation (rightGap i)
 theorem leftClosing_host (i : Fin 3) : (framedGraph.dartPair (leftClosing i)).1=leftVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=1058) (m:=2632) host permutation rotationCertificate rfl (leftGap i)).trans (left_host i)
 theorem rightClosing_host (i : Fin 6) : (framedGraph.dartPair (rightClosing i)).1=rightVertex i :=
  (IndexedRotationCertificate.closingDart_host (n:=1058) (m:=2632) host permutation rotationCertificate rfl (rightGap i)).trans (right_host i)
 theorem typedRows_euler : Fintype.card (Fin 1058)+count typedRows.facePerm=Fintype.card (Fin 2632)+2 :=
  IndexedRotationCertificate.rows_euler (n:=1058) (m:=2632) host permutation rotationCertificate rfl euler
 theorem leftClosing_injective : Function.Injective leftClosing := by
  intro i j he
  apply left_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (leftClosing_host i).symm.trans (hh.trans (leftClosing_host j))
 theorem rightClosing_injective : Function.Injective rightClosing := by
  intro i j he
  apply right_injective
  have hh:=congrArg (fun a=>(framedGraph.dartPair a).1) he
  exact (rightClosing_host i).symm.trans (hh.trans (rightClosing_host j))
 theorem leftMarkers_successor (i : Fin 2) :
    typedRows.facePerm (reversePerm _ (leftClosing i.succ))=reversePerm _ (leftClosing i.castSucc) :=
  IndexedRotationCertificate.closing_marker_successor (n:=1058) (m:=2632) host permutation rotationCertificate rfl _ _ (left_successor i)
 theorem rightMarkers_successor (i : Fin 5) :
    typedRows.facePerm (reversePerm _ (rightClosing i.castSucc))=reversePerm _ (rightClosing i.succ) :=
  IndexedRotationCertificate.closing_marker_successor (n:=1058) (m:=2632) host permutation rotationCertificate rfl _ _ (right_successor i)
end FanFramed
end PlanarHom.ColoringMacroFaces
