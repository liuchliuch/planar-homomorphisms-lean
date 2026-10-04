import PlanarHom.ColoringFramedBoundaryRestriction
import PlanarHom.ColoringFramedPrivateRows
import PlanarHom.ListRotationFilterTransport

noncomputable section
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree

def PrivateRetention : Prop := ∀s (w : LocalPatch.Private s),
  ((FramedMacro.cutRow s (FramedMacro.oldVertex s w.val)).filterMap (FramedMacro.keepDart s)).formPerm=
    ((MacroRows.numericRows s).row w.val).formPerm

theorem sourceBlock_private (f : NumericFormula) (i : Canvas.Index f) (w : Canvas.Private f i) :
    sourceBlock f i (.inr ⟨i,w⟩)=((MacroRows.numericRows (canvasCell f i).shape).row w.val).map (sourceDart f i) := by
  unfold sourceBlock
  change (PortPatchAssembly.localRowWord (Canvas.patch f) (Canvas.port f) _ _ i
    (PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i (.inr w))).map _=_
  rw [PortPatchAssembly.localRowWord_preimage (Canvas.patch f) (Canvas.port f) _ _ i (.inr w)
    (Canvas.localVertices_nodup f i) (Canvas.localVertices_mem f i _) (Canvas.placeVertex_injective f i)]
  rw [MacroRows.localRows_row,LocalPatch.localVertexParts_private]
  rfl

theorem sourceBlock_private_other (f : NumericFormula) (i j : Canvas.Index f) (w : Canvas.Private f i)
    (hji : j≠i) : sourceBlock f j (.inr ⟨i,w⟩)=[] := by
  have hz : PortPatchAssembly.localRowWord (Canvas.patch f) (Canvas.port f)
      (fun i=>MacroRows.localRows (canvasCell f i).shape) (Canvas.localVertices f) j (.inr ⟨i,w⟩)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro u _
    have hn : PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) j u≠.inr ⟨i,w⟩ := by
      cases u with
      | inl p => intro he; cases he
      | inr z => exact fun he=>hji (congrArg Sigma.fst (Sum.inr.inj he))
    exact if_neg hn
  simp only [sourceBlock,hz,List.map_nil]

theorem source_private_row (f : NumericFormula) (i : Canvas.Index f) (w : Canvas.Private f i) :
    (Canvas.geometricRows f).row (.inr ⟨i,w⟩)=
      ((MacroRows.numericRows (canvasCell f i).shape).row w.val).map (sourceDart f i) := by
  let result:=((MacroRows.numericRows (canvasCell f i).shape).row w.val).map (sourceDart f i)
  change ((List.finRange (canvas f).length).reverse.flatMap (fun j=>sourceBlock f j (.inr ⟨i,w⟩)))=result
  have hw (j : Canvas.Index f) : sourceBlock f j (.inr ⟨i,w⟩)=if j=i then result else [] := by
    by_cases hj : j=i
    · subst j
      rw [if_pos rfl]
      exact sourceBlock_private f i w
    · rw [if_neg hj]
      exact sourceBlock_private_other f i j w hj
  simp_rw [hw]
  exact PortPatchAssembly.selectWord_eq _ (List.nodup_reverse.mpr (List.nodup_finRange _)) i
    (List.mem_reverse.mpr (List.mem_finRange i)) (fun _=>result)

theorem sourceDart_injective (f : NumericFormula) (i : Canvas.Index f) : Function.Injective (sourceDart f i) :=
  PortPatchAssembly.liftPatchDart_injective (E:=Canvas.PatchEdge f) i

theorem private_row_filter_perm (hlocal : PrivateRetention) (f : NumericFormula) (i : Canvas.Index f)
    (w : Canvas.Private f i) (a : MultiGraph.Kasteleyn.Dart (LocalPatch.Edge (canvasCell f i).shape)) :
    (((fullRows f).row (.inl (.inr ⟨i,w⟩))).filterMap (keepDart f)).formPerm (sourceDart f i a)=
      ((Canvas.geometricRows f).row (.inr ⟨i,w⟩)).formPerm (sourceDart f i a) := by
  rw [fullRows_private,filter_patchDart,source_private_row]
  rw [ListRotationErasure.formPerm_map_apply _ (sourceDart_injective f i),
    ListRotationErasure.formPerm_map_apply _ (sourceDart_injective f i),hlocal]

theorem retained_row_rotation (hport : PortRetention) (hprivate : PrivateRetention) (f : NumericFormula)
    (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    (((fullRows f).row (.inl ((Canvas.graph f).dartPair a).1)).filterMap (keepDart f)).formPerm a=
      (Canvas.geometricRows f).rotation a := by
  obtain ⟨⟨i,e⟩,b⟩:=a
  have hh : ((Canvas.graph f).dartPair (sourceDart f i (e,b))).1=
      PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i ((Canvas.patch f i).dartPair (e,b)).1 := by
    cases b <;> rfl
  change (((fullRows f).row (.inl ((Canvas.graph f).dartPair (sourceDart f i (e,b))).1)).filterMap (keepDart f)).formPerm _=
    ((Canvas.geometricRows f).row ((Canvas.graph f).dartPair (sourceDart f i (e,b))).1).formPerm _
  rw [hh]
  cases hu : ((Canvas.patch f i).dartPair (e,b)).1 with
  | inl p =>
    change (((fullRows f).row (.inl (.inl (Canvas.port f i p)))).filterMap (keepDart f)).formPerm _=_
    rw [boundary_row_filter hport]
    rfl
  | inr w =>
    exact private_row_filter_perm hprivate f i w (e,b)

end PlanarHom.ColoringEmitter.FramedCanvas
