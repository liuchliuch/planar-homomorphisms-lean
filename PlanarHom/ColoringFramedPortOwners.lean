import PlanarHom.ColoringFramedGlobalMarkers

/-! Every occurrence at an exposed source vertex is either its one allocated
producer port or one consumed input port. These are the literal six cell shapes
and the proved source signal registry, not an additional ownership predicate. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
namespace FramedMacro

 theorem rightPort_output (c : Cell) (j : Fin (rightCount c.shape)) :
    ∃o : Fin c.shape.outputCount,(rightPort c.shape j).1=c.freshPort o := by
  rcases c with ⟨col,row,s,base,args⟩
  cases s <;> fin_cases j
  all_goals solve
    | refine ⟨⟨0,by dsimp only; decide⟩,?_⟩
      apply Fin.ext
      norm_num [rightPort,Cell.freshPort,CellShape.portCount,CellShape.kind,Kind.template,ParsimoniousBlockTemplate.crossover,ParsimoniousBlockTemplate.fanout,ParsimoniousBlockTemplate.equality]
    | refine ⟨⟨1,by dsimp only; decide⟩,?_⟩
      apply Fin.ext
      norm_num [rightPort,Cell.freshPort,CellShape.portCount,CellShape.kind,Kind.template,ParsimoniousBlockTemplate.crossover,ParsimoniousBlockTemplate.fanout,ParsimoniousBlockTemplate.equality]


 theorem port_input_or_output (c : Cell) (p : LocalPatch.Port c.shape) :
    (∃j : Fin (leftCount c.shape),p=leftPort c.shape j) ∨
      ∃o : Fin c.shape.outputCount,p.1=c.freshPort o := by
  obtain ⟨j,rfl⟩ := (portEquiv c.shape).surjective p
  cases j with
  | inl j => exact Or.inl ⟨j,rfl⟩
  | inr j =>
      obtain ⟨o,ho⟩ := rightPort_output c j
      exact Or.inr ⟨o,ho⟩
end FramedMacro
namespace FramedCanvas

 theorem port_origin_cases (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f)
    (p : LocalPatch.Port (canvasCell f i).shape) :
    (∃j : Fin (sharedPred f i+1),p=FramedMacro.leftPort (canvasCell f i).shape (sharedIndex f i j)) ∨
      ∃o : Fin (canvasCell f i).shape.outputCount,
        p.1=(canvasCell f i).freshPort o ∧
        (Canvas.signalEquiv f hf).symm (Canvas.port f i p).1=.inr ⟨i,o⟩ := by
  rcases FramedMacro.port_input_or_output (canvasCell f i) p with ⟨j,hj⟩ | ⟨o,ho⟩
  · exact Or.inl ⟨(sharedIndex f i).symm j,by simpa using hj⟩
  · right
    refine ⟨o,ho,?_⟩
    change (Canvas.signalEquiv f hf).symm (boundaryPort f i p.1)=_
    rw [ho,←Canvas.signalEquiv_output f hf i o,Equiv.symm_apply_apply]

/-- Any two non-input occurrences at one boundary signal are the identical
producer cell and output slot; channels are retained separately by `port`. -/
 theorem output_port_unique (f : NumericFormula) (hf : NumericValid f)
    (i j : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (p : Fin (canvasCell f j).shape.outputCount) (a b : Fin 3)
    (h : Canvas.port f i ((canvasCell f i).freshPort o,a)=
      Canvas.port f j ((canvasCell f j).freshPort p,b)) :
    (⟨i,o⟩ : (i:Canvas.Index f)×Fin (canvasCell f i).shape.outputCount)=⟨j,p⟩ ∧ a=b := by
  have hs := congrArg (fun z : Canvas.BoundaryTriple f => (Canvas.signalEquiv f hf).symm z.1) h
  change (Canvas.signalEquiv f hf).symm (boundaryPort f i ((canvasCell f i).freshPort o))=
    (Canvas.signalEquiv f hf).symm (boundaryPort f j ((canvasCell f j).freshPort p)) at hs
  rw [←Canvas.signalEquiv_output f hf i o,←Canvas.signalEquiv_output f hf j p,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply] at hs
  exact ⟨Sum.inr.inj hs,congrArg Prod.snd h⟩
end FramedCanvas
end PlanarHom.ColoringEmitter
