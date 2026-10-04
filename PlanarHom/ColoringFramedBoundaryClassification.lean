import PlanarHom.ColoringFramedBoundaryWords
import PlanarHom.ColoringFramedBlockEndings

/-! Complete literal boundary-row classification: one producer block when
unconsumed, or consumer block followed by producer block when consumed. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram ParsimoniousNorOneInThree

 theorem fullRows_boundary_consumer (f : NumericFormula) (hf : NumericValid f) (x : InputIndex f) :
    (fullRows f).row (.inl (.inl (inputTriple f x)))=
      consumerBlock f x++producerBlock f hf (inputTriple f x) := by
  generalize ho : (Canvas.signalEquiv f hf).symm (inputTriple f x).1=a
  cases a with
  | inl i => exact fullRows_boundary_initial_consumer f hf _ x rfl i ho
  | inr a => obtain ⟨j,o⟩ := a; exact fullRows_boundary_output_consumer f hf _ x rfl j o ho

 theorem fullRows_boundary_unconsumed (f : NumericFormula) (hf : NumericValid f)
    (b : Canvas.BoundaryTriple f) (hn : ∀x : InputIndex f,inputTriple f x≠b) :
    (fullRows f).row (.inl (.inl b))=producerBlock f hf b := by
  generalize ho : (Canvas.signalEquiv f hf).symm b.1=a
  cases a with
  | inl a =>
      rw [fullRows_word]
      have he : ∀i : Canvas.Index f,patchWord f i (.inl (.inl b))=[] := by
        intro i
        apply patchWord_only_consumer_or_producer f hf b i
        · intro j; exact hn ⟨i,j⟩
        · intro o he; rw [ho] at he; cases he
      simp_rw [he]
      rw [show ((List.finRange (canvas f).length).reverse.flatMap (fun _ => ([] : List (Dart f))))=[] from
        List.flatMap_eq_nil_iff.mpr (fun _ _=>rfl),List.nil_append,seedWord_initial f hf b a ho]
      simp only [producerBlock,ho]
  | inr a =>
      obtain ⟨j,o⟩ := a
      rw [fullRows_word,seedWord_output f hf b j o ho,List.append_nil]
      have he : ∀i : Canvas.Index f,patchWord f i (.inl (.inl b))=
          if i=j then producerBlock f hf b else [] := by
        intro i
        by_cases hij : i=j
        · subst i; rw [if_pos rfl]; exact patchWord_producer f hf b j o ho
        · rw [if_neg hij]
          exact patchWord_only_consumer_or_producer f hf b i
            (fun k=>hn ⟨i,k⟩) (producer_cell_unique f hf b j o ho i hij)
      simp_rw [he]
      exact PortPatchAssembly.selectWord_eq _ (List.nodup_reverse.mpr (List.nodup_finRange _))
        j (by simp) (fun _=>producerBlock f hf b)

 theorem consumerBlock_ending (f : NumericFormula) (x : InputIndex f) :
    ∃xs : List (Dart f),consumerBlock f x=xs++[reversePerm (Edge f) (newMarker f x.1 x.2)] := by
  obtain ⟨xs,hxs⟩ := patchBlock_ending f x.1 (inputPortAt f x)
  refine ⟨xs,?_⟩
  simpa only [consumerBlock,inputPortAt,FramedMacro.portClosing_left,newMarker,reverse_patch_reverse] using hxs

 theorem producerBlock_ending (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f) :
    ∃xs : List (Dart f),producerBlock f hf b=xs++[reversePerm (Edge f) (producerMarker f hf b)] := by
  generalize ho : (Canvas.signalEquiv f hf).symm b.1=a
  cases a with
  | inl i =>
      obtain ⟨xs,hxs⟩ := seedBlock_ending f (initialVertex f i b.2)
      refine ⟨xs,?_⟩
      simpa only [producerBlock,producerMarker,ho,reversePerm,seedDart,Equiv.coe_fn_mk,Bool.not_true] using hxs
  | inr a =>
      obtain ⟨i,o⟩ := a
      obtain ⟨xs,hxs⟩ := patchBlock_ending f i ((canvasCell f i).freshPort o,b.2)
      refine ⟨xs,?_⟩
      simpa only [producerBlock,producerMarker,ho,reverse_patch_reverse] using hxs

 theorem consumerBlock_base (f : NumericFormula) (x : InputIndex f) (a : Dart f)
    (ha : a∈consumerBlock f x) : baseRotation f a=(consumerBlock f x).formPerm a :=
  blockWord_baseRotation f (some x.1) _ a ha

 theorem producerBlock_base (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (a : Dart f) (ha : a∈producerBlock f hf b) :
    baseRotation f a=(producerBlock f hf b).formPerm a := by
  unfold producerBlock at ha ⊢
  cases h : (Canvas.signalEquiv f hf).symm b.1 with
  | inl i => simp only [h] at ha; exact blockWord_baseRotation f none _ a ha
  | inr p => obtain ⟨i,o⟩ := p; simp only [h] at ha; exact blockWord_baseRotation f (some i) _ a ha
end PlanarHom.ColoringEmitter.FramedCanvas
