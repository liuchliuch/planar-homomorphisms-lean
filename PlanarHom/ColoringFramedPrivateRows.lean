import PlanarHom.ColoringFramedCanvasRowWords
import PlanarHom.ColoringFramedMarkerHosts

/-! NEW exact single-block rows at all original private and added frame
vertices. No source splice marker is hosted at any of these vertices. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram ParsimoniousNorOneInThree

 theorem place_private (f : NumericFormula) (i : Canvas.Index f) (w : Canvas.Private f i) :
    placeMacroVertex f i (FramedMacro.oldVertex _ w.val)=.inl (.inr ⟨i,w⟩) := by
  rw [place_oldVertex]
  rw [←LocalPatch.localVertexParts_private,Equiv.symm_apply_apply]
  rfl

 theorem place_corner (f : NumericFormula) (i : Canvas.Index f) (k : Fin 4) :
    placeMacroVertex f i (FramedMacro.vertexParts _ (.inr k))=.inr (i,k) := by
  simp only [placeMacroVertex,Equiv.symm_apply_apply,Sum.elim_inr]

 theorem place_private_index (f : NumericFormula) (i j : Canvas.Index f) (w : Canvas.Private f i)
    (v : Fin (FramedMacro.vertexCount (canvasCell f j).shape))
    (he : placeMacroVertex f j v=.inl (.inr ⟨i,w⟩)) : j=i := by
  unfold placeMacroVertex at he
  cases hv : (FramedMacro.vertexParts (canvasCell f j).shape).symm v with
  | inr k => rw [hv] at he; cases he
  | inl u =>
      rw [hv] at he
      simp only [Sum.elim_inl] at he
      cases hu : (LocalPatch.localVertexParts (canvasCell f j).shape).symm u with
      | inl p => rw [hu] at he; cases he
      | inr z =>
          rw [hu] at he
          exact congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj he))

 theorem place_corner_index (f : NumericFormula) (i j : Canvas.Index f) (k : Fin 4)
    (v : Fin (FramedMacro.vertexCount (canvasCell f j).shape))
    (he : placeMacroVertex f j v=.inr (i,k)) : j=i := by
  unfold placeMacroVertex at he
  cases hv : (FramedMacro.vertexParts (canvasCell f j).shape).symm v with
  | inl u => rw [hv] at he; cases he
  | inr z =>
      rw [hv] at he
      exact congrArg Prod.fst (Sum.inr.inj he)

 theorem fullRows_single_patch (f : NumericFormula) (i : Canvas.Index f)
    (a : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) (v : Vertex f)
    (ha : placeMacroVertex f i a=v)
    (hother : ∀j : Canvas.Index f,j≠i→∀w,placeMacroVertex f j w≠v)
    (hseed : ∀w,seedVertex f w≠v) :
    (fullRows f).row v=(FramedMacro.cutRow (canvasCell f i).shape a).map (patchDart f i) := by
  rw [fullRows_word,seedWord_eq_nil f v hseed,List.append_nil]
  have hw (j : Canvas.Index f) : patchWord f j v=
      if j=i then (FramedMacro.cutRow (canvasCell f i).shape a).map (patchDart f i) else [] := by
    by_cases hj : j=i
    · subst j
      rw [if_pos rfl,←ha,patchWord_preimage]
    · rw [if_neg hj]
      exact patchWord_eq_nil f j v (hother j hj)
  simp_rw [hw]
  exact PortPatchAssembly.selectWord_eq _ (List.nodup_reverse.mpr (List.nodup_finRange _)) i
    (List.mem_reverse.mpr (List.mem_finRange i)) (fun _=>(FramedMacro.cutRow (canvasCell f i).shape a).map (patchDart f i))

 theorem fullRows_private (f : NumericFormula) (i : Canvas.Index f) (w : Canvas.Private f i) :
    (fullRows f).row (.inl (.inr ⟨i,w⟩))=
      (FramedMacro.cutRow (canvasCell f i).shape (FramedMacro.oldVertex _ w.val)).map (patchDart f i) := by
  apply fullRows_single_patch f i _ _ (place_private f i w)
  · intro j hji v he
    exact hji (place_private_index f i j w v he)
  · intro v he
    cases he

 theorem fullRows_corner (f : NumericFormula) (i : Canvas.Index f) (k : Fin 4) :
    (fullRows f).row (.inr (i,k))=
      (FramedMacro.cutRow (canvasCell f i).shape (FramedMacro.vertexParts _ (.inr k))).map (patchDart f i) := by
  apply fullRows_single_patch f i _ _ (place_corner f i k)
  · intro j hji v he
    exact hji (place_corner_index f i j k v he)
  · intro v he
    cases he

 theorem private_ne_inputTriple (f : NumericFormula) (i : Canvas.Index f) (w : Canvas.Private f i) (p : InputIndex f) :
    (Sum.inl (Sum.inr ⟨i,w⟩) : Vertex f)≠.inl (.inl (inputTriple f p)) := by intro h; cases h
 theorem corner_ne_inputTriple (f : NumericFormula) (i : Canvas.Index f) (k : Fin 4) (p : InputIndex f) :
    (Sum.inr (i,k) : Vertex f)≠.inl (.inl (inputTriple f p)) := by intro h; cases h

 theorem private_ne_oldMarker_host (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f)
    (w : Canvas.Private f i) (p : InputIndex f) :
    (Sum.inl (Sum.inr ⟨i,w⟩) : Vertex f)≠((graph f).dartPair (reversePerm (Edge f) (oldMarker f hf p.1 p.2))).1 := by
  rw [oldMarker_reverse_host]
  exact private_ne_inputTriple f i w p
 theorem corner_ne_oldMarker_host (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f)
    (k : Fin 4) (p : InputIndex f) :
    (Sum.inr (i,k) : Vertex f)≠((graph f).dartPair (reversePerm (Edge f) (oldMarker f hf p.1 p.2))).1 := by
  rw [oldMarker_reverse_host]
  exact corner_ne_inputTriple f i k p
 theorem private_ne_newMarker_host (f : NumericFormula) (i : Canvas.Index f)
    (w : Canvas.Private f i) (p : InputIndex f) :
    (Sum.inl (Sum.inr ⟨i,w⟩) : Vertex f)≠((graph f).dartPair (reversePerm (Edge f) (newMarker f p.1 p.2))).1 := by
  rw [newMarker_reverse_host]
  exact private_ne_inputTriple f i w p
 theorem corner_ne_newMarker_host (f : NumericFormula) (i : Canvas.Index f)
    (k : Fin 4) (p : InputIndex f) :
    (Sum.inr (i,k) : Vertex f)≠((graph f).dartPair (reversePerm (Edge f) (newMarker f p.1 p.2))).1 := by
  rw [newMarker_reverse_host]
  exact corner_ne_inputTriple f i k p

end PlanarHom.ColoringEmitter.FramedCanvas
