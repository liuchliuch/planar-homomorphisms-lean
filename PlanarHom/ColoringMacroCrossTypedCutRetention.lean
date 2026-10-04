import PlanarHom.IndexedRotationRowDecode
import PlanarHom.ColoringFramedTypedRows
import PlanarHom.ColoringMacroCrossFramedCutRetention
import PlanarHom.ColoringMacroCrossFramedRawRowBounds

/-! NEW exact typed comparison with the frozen numeric row and cut tables. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringMacroFaces.CrossFramed
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization IndexedRotationCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def referenceRow (v : Fin 1274) : List (Dart (Fin 3168)) := mappedRow numericRow v

theorem numericRow_nodup_clean (v : Fin 1274) : (numericRow v).Nodup := by
  simpa only [Nat.mod_eq_of_lt v.isLt,Fin.eta] using row_nodup v

theorem numericRow_mem_iff (v : Fin 1274) (a : Fin 6336) : a∈numericRow v↔host a=v := by
  constructor
  · exact numericRow_host v a
  · intro h
    rw [←h]
    simpa only [Nat.mod_eq_of_lt a.isLt,Fin.eta] using row_complete a

theorem referenceRow_nodup (v : Fin 1274) : (referenceRow v).Nodup :=
  mappedRow_nodup (n:=1274) (m:=3168) numericRow numericRow_nodup_clean v

theorem referenceRow_eq_raw (v : Fin 1274) :
    referenceRow v=(rawRowValue v.val).map (decodeRaw 3168 (by decide)) := by
  simp only [referenceRow,mappedRow,numericRow,List.map_map]
  rfl

theorem typedRow_formPerm (v : Fin 1274) :
    (typedRows.row v).formPerm=(referenceRow v).formPerm :=
  mappedRow_formPerm (n:=1274) (m:=3168) host permutation rotationCertificate rfl
    numericRow numericRow_mem_iff numericRow_rotation v

theorem referenceRow_filter_erase (v : Fin 1270) :
    (((referenceRow ⟨v.val,by omega⟩).filterMap (keepPrefix 3168 3152)).map (fun a=>(a.1.val,a.2)))=
      ColoringCrossMacroRows.raw v := by
  rw [referenceRow_eq_raw]
  have hh:=filter_decodeRaw 3168 3152 (by decide) (rawRowValue v.val)
    (rawRow_bound ⟨v.val,by omega⟩)
  change _=retainedRawRow v at hh
  exact hh.trans (by simpa only [Nat.mod_eq_of_lt v.isLt,Fin.eta] using row_retained v)

theorem typedRow_cut_left (i : Fin 6) :
    (typedRows.row (leftVertex i)).rotate ((typedRows.row (leftVertex i)).idxOf (leftClosing i)+1)=
      (cutRawRow (leftVertex i) (leftGap i)).map (decodeRaw 3168 (by decide)) := by
  let k:=(rawRowValue (leftVertex i).val).idxOf (closingValue (leftGap i))+1
  have hr : (referenceRow (leftVertex i)).rotate k=
      (cutRawRow (leftVertex i) (leftGap i)).map (decodeRaw 3168 (by decide)) := by
    rw [referenceRow_eq_raw,←List.map_rotate]
    rfl
  have hend : ((referenceRow (leftVertex i)).rotate k).getLast?=some (leftClosing i) := by
    rw [hr,List.getLast?_map,left_cut_last,Option.map_some,closingValue_eq,decodeRaw_closing]
    rfl
  exact (rows_cut_eq_mapped_rotate (n:=1274) (m:=3168) host permutation rotationCertificate rfl
    numericRow numericRow_nodup_clean numericRow_mem_iff numericRow_rotation
    (leftVertex i) (leftClosing i) k (leftClosing_host i) hend).trans hr

theorem typedRow_cut_left_filter_erase (i : Fin 6) :
    ((((typedRows.row (leftVertex i)).rotate ((typedRows.row (leftVertex i)).idxOf (leftClosing i)+1)).filterMap
      (keepPrefix 3168 3152)).map (fun a=>(a.1.val,a.2)))=ColoringCrossMacroRows.raw (leftOldVertex i) := by
  rw [typedRow_cut_left]
  have hh:=filter_decodeRaw 3168 3152 (by decide) (cutRawRow (leftVertex i) (leftGap i))
    (fun d hd=>rawRow_bound (leftVertex i) d (List.mem_rotate.mp hd))
  change _=retainedCutRawRow (leftVertex i) (leftGap i) at hh
  exact hh.trans (left_retained_cut i)

theorem typedRow_cut_right (i : Fin 6) :
    (typedRows.row (rightVertex i)).rotate ((typedRows.row (rightVertex i)).idxOf (rightClosing i)+1)=
      (cutRawRow (rightVertex i) (rightGap i)).map (decodeRaw 3168 (by decide)) := by
  let k:=(rawRowValue (rightVertex i).val).idxOf (closingValue (rightGap i))+1
  have hr : (referenceRow (rightVertex i)).rotate k=
      (cutRawRow (rightVertex i) (rightGap i)).map (decodeRaw 3168 (by decide)) := by
    rw [referenceRow_eq_raw,←List.map_rotate]
    rfl
  have hend : ((referenceRow (rightVertex i)).rotate k).getLast?=some (rightClosing i) := by
    rw [hr,List.getLast?_map,right_cut_last,Option.map_some,closingValue_eq,decodeRaw_closing]
    rfl
  exact (rows_cut_eq_mapped_rotate (n:=1274) (m:=3168) host permutation rotationCertificate rfl
    numericRow numericRow_nodup_clean numericRow_mem_iff numericRow_rotation
    (rightVertex i) (rightClosing i) k (rightClosing_host i) hend).trans hr

theorem typedRow_cut_right_filter_erase (i : Fin 6) :
    ((((typedRows.row (rightVertex i)).rotate ((typedRows.row (rightVertex i)).idxOf (rightClosing i)+1)).filterMap
      (keepPrefix 3168 3152)).map (fun a=>(a.1.val,a.2)))=ColoringCrossMacroRows.raw (rightOldVertex i) := by
  rw [typedRow_cut_right]
  have hh:=filter_decodeRaw 3168 3152 (by decide) (cutRawRow (rightVertex i) (rightGap i))
    (fun d hd=>rawRow_bound (rightVertex i) d (List.mem_rotate.mp hd))
  change _=retainedCutRawRow (rightVertex i) (rightGap i) at hh
  exact hh.trans (right_retained_cut i)

end PlanarHom.ColoringMacroFaces.CrossFramed
