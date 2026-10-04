import PlanarHom.ColoringFramedBaseRotation
import PlanarHom.ColoringFramedMarkerHosts
import PlanarHom.RotationCutEnding

/-! Literal local blocks end at precisely the reversed face markers used by
the canonical splice program. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram ParsimoniousNorOneInThree
namespace FramedMacro

 theorem cutRow_port_ending (s : CellShape) (p : LocalPatch.Port s) :
    ∃xs : List (MultiGraph.Kasteleyn.Dart (Fin (edgeCount s))),
      cutRow s (portVertex s p)=xs++[portClosing s p] := by
  rw [cutRow_port]
  apply PlanarHom.rotate_after_idxOf_ending
  · exact (rows s).nodup _
  · apply ((rows s).mem _ _).mpr
    exact portClosing_host_oldPort s p
end FramedMacro
namespace FramedCanvas

 theorem patchBlock_ending (f : NumericFormula) (i : Canvas.Index f)
    (p : LocalPatch.Port (canvasCell f i).shape) :
    ∃xs : List (Dart f),blockWord f (some i) (FramedMacro.portVertex (canvasCell f i).shape p)=
      xs++[patchDart f i (FramedMacro.portClosing (canvasCell f i).shape p)] := by
  obtain ⟨xs,hxs⟩ := FramedMacro.cutRow_port_ending (canvasCell f i).shape p
  refine ⟨xs.map (patchDart f i),?_⟩
  change (FramedMacro.cutRow (canvasCell f i).shape (FramedMacro.portVertex (canvasCell f i).shape p)).map (patchDart f i)=_
  rw [hxs,List.map_append]
  rfl

 theorem seedBlock_ending (f : NumericFormula) (v : Fin (3*f.1)) :
    ∃xs : List (Dart f),blockWord f none v=xs++[seedDart f ((finRotate (3*f.1)).symm v,false)] :=
  ⟨[seedDart f (v,true)],rfl⟩
end FramedCanvas
end PlanarHom.ColoringEmitter
