import PlanarHom.ColoringMacroTestTypedCutRetention
import PlanarHom.ColoringMacroWireTypedCutRetention
import PlanarHom.ColoringMacroCrossTypedCutRetention
import PlanarHom.ColoringMacroFanTypedCutRetention
import PlanarHom.ColoringFramedLocalRetention
import PlanarHom.ColoringFramedMarkerHosts

/-! NEW final typed cut/filter adapter. The exposed port rows retain their
literal linear order; other vertex rows retain their exact cyclic permutation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedMacro
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram
open IndexedRotationCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def referenceRow : (s : CellShape)→Fin (vertexCount s)→List (Dart (Fin (edgeCount s)))
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.referenceRow
  | .cross => ColoringMacroFaces.CrossFramed.referenceRow
  | .fan => ColoringMacroFaces.FanFramed.referenceRow
  | .test => ColoringMacroFaces.TestFramed.referenceRow

theorem referenceRow_nodup (s : CellShape) (v : Fin (vertexCount s)) : (referenceRow s v).Nodup := by
  cases s
  all_goals first
    | exact ColoringMacroFaces.WireFramed.referenceRow_nodup v
    | exact ColoringMacroFaces.CrossFramed.referenceRow_nodup v
    | exact ColoringMacroFaces.FanFramed.referenceRow_nodup v
    | exact ColoringMacroFaces.TestFramed.referenceRow_nodup v

theorem row_formPerm_reference (s : CellShape) (v : Fin (vertexCount s)) :
    ((rows s).row v).formPerm=(referenceRow s v).formPerm := by
  cases s
  all_goals first
    | exact ColoringMacroFaces.WireFramed.typedRow_formPerm v
    | exact ColoringMacroFaces.CrossFramed.typedRow_formPerm v
    | exact ColoringMacroFaces.FanFramed.typedRow_formPerm v
    | exact ColoringMacroFaces.TestFramed.typedRow_formPerm v

theorem eraseDart_injective (k : ℕ) : Function.Injective (fun a : Dart (Fin k)=>(a.1.val,a.2)) := by
  intro a b h
  exact Prod.ext (Fin.ext (congrArg (fun p : ℕ×Bool=>p.1) h)) (congrArg (fun p : ℕ×Bool=>p.2) h)

theorem referenceRow_filter (s : CellShape) (v : LocalPatch.NumericVertex s) :
    (referenceRow s (oldVertex s v)).filterMap (keepDart s)=(MacroRows.numericRows s).row v := by
  apply (List.map_injective_iff.mpr (eraseDart_injective _))
  rw [MacroRows.numericRows_erase]
  cases s
  all_goals first
    | exact ColoringMacroFaces.WireFramed.referenceRow_filter_erase (ColoringWireMacroEmitterJoin.vertexIndex v)
    | exact ColoringMacroFaces.CrossFramed.referenceRow_filter_erase (ColoringCrossMacroEmitterJoin.vertexIndex v)
    | exact ColoringMacroFaces.FanFramed.referenceRow_filter_erase (ColoringFanMacroEmitterJoin.vertexIndex v)
    | exact ColoringMacroFaces.TestFramed.referenceRow_filter_erase (ColoringTestMacroEmitterJoin.vertexIndex v)

theorem cutRow_formPerm_reference (s : CellShape) (v : Fin (vertexCount s)) :
    (cutRow s v).formPerm=(referenceRow s v).formPerm := by
  unfold cutRow
  split_ifs
  · rw [List.formPerm_rotate _ ((rows s).nodup v)]
    exact row_formPerm_reference s v
  · exact row_formPerm_reference s v

theorem cutRow_filter_formPerm (s : CellShape) (v : LocalPatch.NumericVertex s) :
    ((cutRow s (oldVertex s v)).filterMap (keepDart s)).formPerm=
      ((MacroRows.numericRows s).row v).formPerm := by
  have hh:=ListRotationErasure.filterMap_formPerm_eq (keepDart s) (keepDart_partial_injective s)
    (cutRow s (oldVertex s v)) (referenceRow s (oldVertex s v))
    ((cutRows s).nodup _) (referenceRow_nodup s _) (cutRow_formPerm_reference s _)
  exact hh.trans (congrArg List.formPerm (referenceRow_filter s v))

theorem portVertex_left (s : CellShape) (i : Fin (leftCount s)) :
    portVertex s (leftPort s i)=leftVertex s i := by
  have hh:=portClosing_host_oldPort s (leftPort s i)
  rw [portClosing_left,left_host] at hh
  exact hh.symm

theorem portVertex_right (s : CellShape) (i : Fin (rightCount s)) :
    portVertex s (rightPort s i)=rightVertex s i := by
  have hh:=portClosing_host_oldPort s (rightPort s i)
  rw [portClosing_right,right_host] at hh
  exact hh.symm

theorem cutRow_filter_left (s : CellShape) (i : Fin (leftCount s)) :
    (cutRow s (portVertex s (leftPort s i))).filterMap (keepDart s)=
      (MacroRows.numericRows s).row (LocalPatch.portVertex s (leftPort s i)) := by
  apply (List.map_injective_iff.mpr (eraseDart_injective _))
  rw [MacroRows.numericRows_erase,cutRow_port,portVertex_left,portClosing_left]
  cases s
  · have hv : ColoringMacroFaces.WireFramed.leftOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireTop (leftPort .wireTop i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .wireTop i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.WireFramed.leftOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireBottom (leftPort .wireBottom i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .wireBottom i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.WireFramed.leftOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireDown (leftPort .wireDown i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .wireDown i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.CrossFramed.leftOldVertex i=
        ColoringCrossMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .cross (leftPort .cross i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .cross i)).symm
    exact (ColoringMacroFaces.CrossFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringCrossMacroRows.raw hv)
  · have hv : ColoringMacroFaces.FanFramed.leftOldVertex i=
        ColoringFanMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .fan (leftPort .fan i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .fan i)).symm
    exact (ColoringMacroFaces.FanFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringFanMacroRows.raw hv)
  · have hv : ColoringMacroFaces.TestFramed.leftOldVertex i=
        ColoringTestMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .test (leftPort .test i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_left .test i)).symm
    exact (ColoringMacroFaces.TestFramed.typedRow_cut_left_filter_erase i).trans
      (congrArg ColoringTestMacroRows.raw hv)
theorem cutRow_filter_right (s : CellShape) (i : Fin (rightCount s)) :
    (cutRow s (portVertex s (rightPort s i))).filterMap (keepDart s)=
      (MacroRows.numericRows s).row (LocalPatch.portVertex s (rightPort s i)) := by
  apply (List.map_injective_iff.mpr (eraseDart_injective _))
  rw [MacroRows.numericRows_erase,cutRow_port,portVertex_right,portClosing_right]
  cases s
  · have hv : ColoringMacroFaces.WireFramed.rightOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireTop (rightPort .wireTop i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .wireTop i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.WireFramed.rightOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireBottom (rightPort .wireBottom i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .wireBottom i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.WireFramed.rightOldVertex i=
        ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireDown (rightPort .wireDown i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .wireDown i)).symm
    exact (ColoringMacroFaces.WireFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringWireMacroRows.raw hv)
  · have hv : ColoringMacroFaces.CrossFramed.rightOldVertex i=
        ColoringCrossMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .cross (rightPort .cross i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .cross i)).symm
    exact (ColoringMacroFaces.CrossFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringCrossMacroRows.raw hv)
  · have hv : ColoringMacroFaces.FanFramed.rightOldVertex i=
        ColoringFanMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .fan (rightPort .fan i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .fan i)).symm
    exact (ColoringMacroFaces.FanFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringFanMacroRows.raw hv)
  · have hv : ColoringMacroFaces.TestFramed.rightOldVertex i=
        ColoringTestMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .test (rightPort .test i)) := by
      apply Fin.ext
      exact (congrArg Fin.val (portVertex_right .test i)).symm
    exact (ColoringMacroFaces.TestFramed.typedRow_cut_right_filter_erase i).trans
      (congrArg ColoringTestMacroRows.raw hv)

theorem cutRow_filter_port (s : CellShape) (p : LocalPatch.Port s) :
    (cutRow s (portVertex s p)).filterMap (keepDart s)=
      (MacroRows.numericRows s).row (LocalPatch.portVertex s p) := by
  obtain ⟨q,rfl⟩:=(portEquiv s).surjective p
  cases q with
  | inl i => exact cutRow_filter_left s i
  | inr i => exact cutRow_filter_right s i

theorem cutRow_filter_private_formPerm (s : CellShape) (w : LocalPatch.Private s) :
    ((cutRow s (oldVertex s w.val)).filterMap (keepDart s)).formPerm=
      ((MacroRows.numericRows s).row w.val).formPerm := cutRow_filter_formPerm s w.val

end PlanarHom.ColoringEmitter.FramedMacro
