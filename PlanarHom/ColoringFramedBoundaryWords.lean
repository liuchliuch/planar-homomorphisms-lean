import PlanarHom.ColoringFramedBoundaryPreimages
import PlanarHom.OrderedTwoBlockSelection

/-! Exact producer/consumer block classification of canonical framed boundary
rows. Unique source allocation and single input consumption discharge it. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram ParsimoniousNorOneInThree

 def inputPortAt (f : NumericFormula) (x : InputIndex f) : LocalPatch.Port (canvasCell f x.1).shape :=
  FramedMacro.leftPort (canvasCell f x.1).shape (sharedIndex f x.1 x.2)

 def consumerBlock (f : NumericFormula) (x : InputIndex f) : List (Dart f) :=
  blockWord f (some x.1) (FramedMacro.portVertex (canvasCell f x.1).shape (inputPortAt f x))

 def producerBlock (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f) : List (Dart f) :=
  match (Canvas.signalEquiv f hf).symm b.1 with
  | .inl i => blockWord f none (initialVertex f i b.2)
  | .inr ⟨i,o⟩ => blockWord f (some i)
      (FramedMacro.portVertex (canvasCell f i).shape ((canvasCell f i).freshPort o,b.2))

 theorem patchWord_consumer (f : NumericFormula) (x : InputIndex f) :
    patchWord f x.1 (.inl (.inl (inputTriple f x)))=consumerBlock f x :=
  patchWord_boundary f x.1 (inputPortAt f x)

 theorem patchWord_producer (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (ho : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨i,o⟩) :
    patchWord f i (.inl (.inl b))=producerBlock f hf b := by
  have hs := output_origin_signal f hf b i o ho
  have hb : Canvas.port f i ((canvasCell f i).freshPort o,b.2)=b := Prod.ext hs.symm rfl
  simp only [producerBlock,ho]
  rw [←hb,patchWord_boundary]
  rfl

 theorem patchWord_only_consumer_or_producer (f : NumericFormula) (hf : NumericValid f)
    (b : Canvas.BoundaryTriple f) (i : Canvas.Index f)
    (hinput : ∀j : Fin (sharedPred f i+1),inputTriple f ⟨i,j⟩≠b)
    (houtput : ∀o : Fin (canvasCell f i).shape.outputCount,
      (Canvas.signalEquiv f hf).symm b.1≠.inr ⟨i,o⟩) :
    patchWord f i (.inl (.inl b))=[] := by
  apply patchWord_boundary_nil
  intro p hp
  rcases port_origin_cases f hf i p with ⟨j,hj⟩ | ⟨o,_,ho⟩
  · apply hinput j
    simpa only [hj,inputTriple] using hp
  · apply houtput o
    simpa only [hp] using ho

 theorem consumer_cell_unique (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (x : InputIndex f) (hx : inputTriple f x=b) (i : Canvas.Index f) (hi : i≠x.1)
    (j : Fin (sharedPred f i+1)) : inputTriple f ⟨i,j⟩≠b := by
  intro h
  exact hi (congrArg Sigma.fst (inputTriple_injective f hf (h.trans hx.symm)))

 theorem producer_cell_unique (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (ho : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨i,o⟩)
    (j : Canvas.Index f) (hji : j≠i) (p : Fin (canvasCell f j).shape.outputCount) :
    (Canvas.signalEquiv f hf).symm b.1≠.inr ⟨j,p⟩ := by
  intro h
  exact hji (congrArg Sigma.fst (Sum.inr.inj (h.symm.trans ho)))

 theorem producer_before_consumer (f : NumericFormula) (hf : NumericValid f)
    (b : Canvas.BoundaryTriple f) (x : InputIndex f) (hx : inputTriple f x=b)
    (i : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (ho : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨i,o⟩) : i.val<x.1.val := by
  have hb : boundaryPort f x.1 (inputPortAt f x).1=b.1 := congrArg Prod.fst hx
  have h := Canvas.input_origin f hf x.1 (inputPortAt f x).1 (FramedMacro.leftPort_mem _ _)
  rcases h with ⟨a,ha⟩ | ⟨j,p,hj,hp⟩
  · rw [hb,ho] at ha
    cases ha
  · rw [hb,ho] at hp
    have he : i=j := congrArg Sigma.fst (Sum.inr.inj hp)
    simpa only [he] using hj

 theorem fullRows_boundary_initial_consumer (f : NumericFormula) (hf : NumericValid f)
    (b : Canvas.BoundaryTriple f) (x : InputIndex f) (hx : inputTriple f x=b)
    (a : Fin f.1) (ha : (Canvas.signalEquiv f hf).symm b.1=.inl a) :
    (fullRows f).row (.inl (.inl b))=consumerBlock f x++producerBlock f hf b := by
  rw [fullRows_word]
  have he : ∀i : Canvas.Index f,patchWord f i (.inl (.inl b))=
      if i=x.1 then consumerBlock f x else [] := by
    intro i
    by_cases hi : i=x.1
    · subst i
      rw [if_pos rfl,←hx]
      exact patchWord_consumer f x
    · rw [if_neg hi]
      apply patchWord_only_consumer_or_producer f hf b i
      · exact consumer_cell_unique f hf b x hx i hi
      · intro o ho; rw [ha] at ho; cases ho
  simp_rw [he]
  rw [PortPatchAssembly.selectWord_eq _ (List.nodup_reverse.mpr (List.nodup_finRange _)) x.1
    (by simp) (fun _=>consumerBlock f x),seedWord_initial f hf b a ha]
  simp only [producerBlock,ha]

 theorem fullRows_boundary_output_consumer (f : NumericFormula) (hf : NumericValid f)
    (b : Canvas.BoundaryTriple f) (x : InputIndex f) (hx : inputTriple f x=b)
    (j : Canvas.Index f) (o : Fin (canvasCell f j).shape.outputCount)
    (ho : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨j,o⟩) :
    (fullRows f).row (.inl (.inl b))=consumerBlock f x++producerBlock f hf b := by
  have hj := producer_before_consumer f hf b x hx j o ho
  have hne : x.1≠j := by intro h; have := congrArg Fin.val h; omega
  rw [fullRows_word,seedWord_output f hf b j o ho,List.append_nil]
  have he : ∀i : Canvas.Index f,patchWord f i (.inl (.inl b))=
      if i=x.1 then consumerBlock f x else if i=j then producerBlock f hf b else [] := by
    intro i
    by_cases hi : i=x.1
    · subst i
      rw [if_pos rfl,←hx]
      exact patchWord_consumer f x
    · rw [if_neg hi]
      by_cases hij : i=j
      · subst i; rw [if_pos rfl]; exact patchWord_producer f hf b j o ho
      · rw [if_neg hij]
        exact patchWord_only_consumer_or_producer f hf b i
          (consumer_cell_unique f hf b x hx i hi) (producer_cell_unique f hf b j o ho i hij)
  simp_rw [he]
  apply PlanarHom.select_two_words _ (List.nodup_reverse.mpr (List.nodup_finRange _))
    (List.pairwise_lt_finRange _).reverse x.1 j hne (by simp) (by simp)
  exact not_lt_of_ge hj.le
end PlanarHom.ColoringEmitter.FramedCanvas
