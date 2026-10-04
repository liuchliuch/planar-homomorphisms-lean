import PlanarHom.ColoringFramedGlobalMarkers
import PlanarHom.ColoringFramedCanvasGraph

/-! NEW actual framed-graph hosts of the two reversed splice markers. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization
namespace FramedMacro

 theorem boundaryVertex_eq_oldPort (s:CellShape) (q:Fin (leftCount s)⊕Fin (rightCount s)) :
    boundaryVertex s q=oldVertex s (LocalPatch.portVertex s (portEquiv s q)) := by
  cases s <;> revert q <;> decide +kernel

 theorem portClosing_host_oldPort (s:CellShape) (p:LocalPatch.Port s) :
    ((graph s).dartPair (portClosing s p)).1=oldVertex s (LocalPatch.portVertex s p) := by
  rw [portClosing_host,boundaryVertex_eq_oldPort,Equiv.apply_symm_apply]

end FramedMacro
namespace FramedCanvas

 theorem patchDart_host (f:NumericFormula) (i:Canvas.Index f) (a:MultiGraph.Kasteleyn.Dart (PatchEdge f i)) :
    ((graph f).dartPair (patchDart f i a)).1=
      placeMacroVertex f i (((FramedMacro.graph (canvasCell f i).shape).dartPair a).1) := by
  rcases a with ⟨a,b⟩
  cases b <;> rfl

 theorem patchClosing_host (f:NumericFormula) (i:Canvas.Index f) (p:LocalPatch.Port (canvasCell f i).shape) :
    ((graph f).dartPair (patchDart f i (FramedMacro.portClosing (canvasCell f i).shape p))).1=
      .inl (.inl (Canvas.port f i p)) := by
  rw [patchDart_host,FramedMacro.portClosing_host_oldPort,place_oldVertex]
  rw [←LocalPatch.localVertexParts_port,Equiv.symm_apply_apply]
  rfl

 theorem reverse_patch_reverse (f:NumericFormula) (i:Canvas.Index f)
    (a:MultiGraph.Kasteleyn.Dart (PatchEdge f i)) :
    reversePerm (Edge f) (patchDart f i (reversePerm (PatchEdge f i) a))=patchDart f i a := by
  rcases a with ⟨a,b⟩
  cases b <;> rfl

 theorem seedVertex_initialVertex (f:NumericFormula) (i:Fin f.1) (b:Fin 3) :
    seedVertex f (initialVertex f i b)=.inl (.inl (initialBoundary f i,b)) := by
  apply congrArg Sum.inl
  apply congrArg Sum.inl
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (3*i.val+(2-b.val))/3=i.val
      have hb:=b.isLt
      omega
  · apply Fin.ext
    change 2-(3*i.val+(2-b.val))%3=b.val
    have hb:=b.isLt
    omega

 theorem producerMarker_reverse_host (f:NumericFormula) (hf:NumericValid f) (b:Canvas.BoundaryTriple f) :
    ((graph f).dartPair (reversePerm (Edge f) (producerMarker f hf b))).1=.inl (.inl b) := by
  generalize ha:(Canvas.signalEquiv f hf).symm b.1=a
  cases a with
  | inl i =>
    have hb:b.1=initialBoundary f i:=by
      have hh:=congrArg (Canvas.signalEquiv f hf) ha
      simpa only [Equiv.apply_symm_apply,Canvas.signalEquiv_initial] using hh
    simp only [producerMarker,ha]
    change seedVertex f (finRotate (3*f.1) ((finRotate (3*f.1)).symm (initialVertex f i b.2)))=_
    rw [Equiv.apply_symm_apply,seedVertex_initialVertex]
    rw [←hb]
  | inr a =>
    rcases a with ⟨i,o⟩
    have hb:b.1=boundaryPort f i ((canvasCell f i).freshPort o):=by
      have hh:=congrArg (Canvas.signalEquiv f hf) ha
      simpa only [Equiv.apply_symm_apply,Canvas.signalEquiv_output] using hh
    simp only [producerMarker,ha]
    rw [reverse_patch_reverse,patchClosing_host]
    congr 2
    exact Prod.ext hb.symm rfl

 theorem oldMarker_reverse_host (f:NumericFormula) (hf:NumericValid f) (p:InputIndex f) :
    ((graph f).dartPair (reversePerm (Edge f) (oldMarker f hf p.1 p.2))).1=
      .inl (.inl (inputTriple f p)) :=
  producerMarker_reverse_host f hf (inputTriple f p)

 theorem newMarker_reverse_host (f:NumericFormula) (p:InputIndex f) :
    ((graph f).dartPair (reversePerm (Edge f) (newMarker f p.1 p.2))).1=
      .inl (.inl (inputTriple f p)) := by
  unfold newMarker
  rw [reverse_patch_reverse,←FramedMacro.portClosing_left,patchClosing_host]
  rfl

end FramedCanvas
end PlanarHom.ColoringEmitter
