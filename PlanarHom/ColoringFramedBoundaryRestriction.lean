import PlanarHom.ColoringFramedLocalRetention
import PlanarHom.ColoringFramedCanvasRowWords
import PlanarHom.ColoringEmitterComputedRows

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def PortRetention : Prop := ∀s (p : LocalPatch.Port s),
  (FramedMacro.cutRow s (FramedMacro.portVertex s p)).filterMap (FramedMacro.keepDart s)=
    (MacroRows.numericRows s).row (LocalPatch.portVertex s p)

def sourceBlock (f : NumericFormula) (i : Canvas.Index f) (v : Canvas.Vertex f) :
    List (MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :=
  (PortPatchAssembly.localRowWord (Canvas.patch f) (Canvas.port f)
    (fun i=>MacroRows.localRows (canvasCell f i).shape) (Canvas.localVertices f) i v).map
      (PortPatchAssembly.liftPatchDart i)

theorem sourceBlock_port (f : NumericFormula) (i : Canvas.Index f) (p : Canvas.Port f i)
    (b : Canvas.BoundaryTriple f) (hp : Canvas.port f i p=b) :
    sourceBlock f i (.inl b)=((MacroRows.numericRows (canvasCell f i).shape).row
      (LocalPatch.portVertex (canvasCell f i).shape p)).map (sourceDart f i) := by
  have hv : PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i (.inl p)=.inl b := congrArg Sum.inl hp
  unfold sourceBlock
  rw [←hv,PortPatchAssembly.localRowWord_preimage (Canvas.patch f) (Canvas.port f) _ _ i (.inl p)
    (Canvas.localVertices_nodup f i) (Canvas.localVertices_mem f i _) (Canvas.placeVertex_injective f i)]
  rw [MacroRows.localRows_row,LocalPatch.localVertexParts_port]
  rfl

theorem sourceBlock_noport (f : NumericFormula) (i : Canvas.Index f) (b : Canvas.BoundaryTriple f)
    (h : ∀p,Canvas.port f i p≠b) : sourceBlock f i (.inl b)=[] := by
  have hz : PortPatchAssembly.localRowWord (Canvas.patch f) (Canvas.port f)
      (fun i=>MacroRows.localRows (canvasCell f i).shape) (Canvas.localVertices f) i (.inl b)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro v _
    have hn : PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i v≠.inl b := by
      cases v with
      | inl p => exact fun he=>h p (Sum.inl.inj he)
      | inr w => intro he; cases he
    exact if_neg hn
  simp only [sourceBlock,hz,List.map_nil]

theorem place_port (f : NumericFormula) (i : Canvas.Index f) (p : Canvas.Port f i) :
    placeMacroVertex f i (FramedMacro.portVertex (canvasCell f i).shape p)=.inl (.inl (Canvas.port f i p)) := by
  unfold FramedMacro.portVertex
  rw [place_oldVertex,←LocalPatch.localVertexParts_port,Equiv.symm_apply_apply]
  rfl

theorem place_to_boundary (f : NumericFormula) (i : Canvas.Index f)
    (v : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) (b : Canvas.BoundaryTriple f)
    (he : placeMacroVertex f i v=.inl (.inl b)) :
    ∃p,v=FramedMacro.portVertex (canvasCell f i).shape p ∧ Canvas.port f i p=b := by
  unfold placeMacroVertex at he
  cases hv : (FramedMacro.vertexParts (canvasCell f i).shape).symm v with
  | inr k => rw [hv] at he; cases he
  | inl u =>
    rw [hv] at he
    simp only [Sum.elim_inl] at he
    cases hu : (LocalPatch.localVertexParts (canvasCell f i).shape).symm u with
    | inr w => rw [hu] at he; cases he
    | inl p =>
      rw [hu] at he
      have hv' : v=FramedMacro.oldVertex (canvasCell f i).shape u := by
        simpa only [Equiv.apply_symm_apply,FramedMacro.oldVertex] using congrArg (FramedMacro.vertexParts (canvasCell f i).shape) hv
      have hu' : u=LocalPatch.portVertex (canvasCell f i).shape p := by
        simpa only [Equiv.apply_symm_apply,LocalPatch.localVertexParts_port] using congrArg (LocalPatch.localVertexParts (canvasCell f i).shape) hu
      exact ⟨p,hv'.trans (congrArg (FramedMacro.oldVertex (canvasCell f i).shape) hu'),Sum.inl.inj (Sum.inl.inj he)⟩

theorem patchWord_boundary_filter (hlocal : PortRetention) (f : NumericFormula) (i : Canvas.Index f)
    (b : Canvas.BoundaryTriple f) :
    (patchWord f i (.inl (.inl b))).filterMap (keepDart f)=sourceBlock f i (.inl b) := by
  by_cases hp : ∃p,Canvas.port f i p=b
  · obtain ⟨p,hp⟩:=hp
    have hv : placeMacroVertex f i (FramedMacro.portVertex (canvasCell f i).shape p)=.inl (.inl b) := by rw [place_port,hp]
    rw [←hv,patchWord_preimage,filter_patchDart,hlocal]
    exact (sourceBlock_port f i p b hp).symm
  · rw [patchWord_eq_nil]
    · simpa only [List.filterMap_nil] using (sourceBlock_noport f i b (fun p h=>hp ⟨p,h⟩)).symm
    · intro v he
      obtain ⟨p,_,hh⟩:=place_to_boundary f i v b he
      exact hp ⟨p,hh⟩

theorem seedWord_filter (f : NumericFormula) (v : Vertex f) : (seedWord f v).filterMap (keepDart f)=[] := by
  rw [seedWord,List.filterMap_flatMap]
  apply List.flatMap_eq_nil_iff.mpr
  intro w _
  split_ifs
  · exact filter_seedDart f _
  · rfl

theorem boundary_row_filter (hlocal : PortRetention) (f : NumericFormula) (b : Canvas.BoundaryTriple f) :
    ((fullRows f).row (.inl (.inl b))).filterMap (keepDart f)=(Canvas.geometricRows f).row (.inl b) := by
  rw [fullRows_word,List.filterMap_append,seedWord_filter,List.append_nil,List.filterMap_flatMap]
  simp_rw [patchWord_boundary_filter hlocal]
  rfl

end PlanarHom.ColoringEmitter.FramedCanvas
