import PlanarHom.ColoringFramedMarkerInjection

/-! NEW global injectivity of consumed boundary triples and all actual splice
markers. Single consumption is inherited from the literal source frontier run. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization
namespace FramedMacro

 theorem freshPort_ne_leftPort (c:Cell) (o:Fin c.shape.outputCount) (j:Fin (leftCount c.shape)) :
    c.freshPort o≠(leftPort c.shape j).1 := by
  intro h
  have hh:=congrArg Fin.val h
  have hp:=Canvas.leftPort_input c.shape _ (leftPort_mem c.shape j)
  have hc:Macro.inputCount c.shape.kind=c.shape.kind.template.inputs:=by cases c.shape <;> rfl
  rw [hc] at hp
  dsimp only [Cell.freshPort] at hh
  omega

end FramedMacro
namespace FramedCanvas

 abbrev InputIndex (f:NumericFormula) := (i:Canvas.Index f)×Fin (sharedPred f i+1)
 def inputTriple (f:NumericFormula) (p:InputIndex f) : Canvas.BoundaryTriple f :=
  Canvas.port f p.1 (FramedMacro.leftPort (canvasCell f p.1).shape (sharedIndex f p.1 p.2))

 theorem inputTriple_injective (f:NumericFormula) (hf:NumericValid f) : Function.Injective (inputTriple f) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hs:Canvas.inputSignal f ⟨i,⟨(FramedMacro.leftPort (canvasCell f i).shape (sharedIndex f i a)).1,FramedMacro.leftPort_mem _ _⟩⟩=
      Canvas.inputSignal f ⟨j,⟨(FramedMacro.leftPort (canvasCell f j).shape (sharedIndex f j b)).1,FramedMacro.leftPort_mem _ _⟩⟩:=
    congrArg Prod.fst h
  have hij:i=j:=congrArg Sigma.fst (Canvas.inputSignal_injective f hf hs)
  subst j
  have hab:a=b:=(sharedIndex f i).injective (FramedMacro.leftPort_injective _ (Canvas.port_injective f i h))
  subst b
  rfl

 theorem oldMarker_global_injective (f:NumericFormula) (hf:NumericValid f) :
    Function.Injective (fun p:InputIndex f=>oldMarker f hf p.1 p.2) := by
  intro p q h
  exact inputTriple_injective f hf (producerMarker_injective f hf h)

 theorem newMarker_global_injective (f:NumericFormula) :
    Function.Injective (fun p:InputIndex f=>newMarker f p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hij:i=j:=congrArg Sigma.fst (Sum.inr.inj (congrArg Prod.fst h))
  subst j
  have hab:a=b:=newMarker_injective f i h
  subst b
  rfl

 theorem producerMarker_ne_newMarker (f:NumericFormula) (hf:NumericValid f) (b:Canvas.BoundaryTriple f)
    (i:Canvas.Index f) (t:Fin (sharedPred f i+1)) : producerMarker f hf b≠newMarker f i t := by
  intro h
  generalize ha:(Canvas.signalEquiv f hf).symm b.1=a
  cases a with
  | inl a =>
    simp only [producerMarker,ha] at h
    exact Sum.inl_ne_inr (congrArg Prod.fst h)
  | inr a =>
    rcases a with ⟨j,o⟩
    simp only [producerMarker,ha] at h
    have hji:j=i:=congrArg Sigma.fst (Sum.inr.inj (congrArg Prod.fst h))
    subst i
    have hp:((canvasCell f j).freshPort o,b.2)=FramedMacro.leftPort (canvasCell f j).shape (sharedIndex f j t):=by
      apply FramedMacro.portClosing_injective _
      rw [FramedMacro.portClosing_left]
      exact (reversePerm _).injective (patchDart_injective f j h)
    exact FramedMacro.freshPort_ne_leftPort _ o _ (congrArg Prod.fst hp)

 theorem oldMarker_newMarker_disjoint (f:NumericFormula) (hf:NumericValid f) (p q:InputIndex f) :
    oldMarker f hf p.1 p.2≠newMarker f q.1 q.2 :=
  producerMarker_ne_newMarker f hf (inputTriple f p) q.1 q.2

 def inputMarker (f:NumericFormula) (hf:NumericValid f) (p:InputIndex f×Bool) : Dart f :=
  if p.2 then newMarker f p.1.1 p.1.2 else oldMarker f hf p.1.1 p.1.2

 theorem inputMarker_injective (f:NumericFormula) (hf:NumericValid f) : Function.Injective (inputMarker f hf) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  cases a <;> cases b
  · exact Prod.ext (oldMarker_global_injective f hf h) rfl
  · exact (oldMarker_newMarker_disjoint f hf p q h).elim
  · exact (oldMarker_newMarker_disjoint f hf q p h.symm).elim
  · exact Prod.ext (newMarker_global_injective f h) rfl

end FramedCanvas
end PlanarHom.ColoringEmitter
