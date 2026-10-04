import PlanarHom.ColoringFramedCanvasRows
import PlanarHom.ColoringFramedMacroEndpoints

noncomputable section
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree

theorem old_source (f : NumericFormula) (e : Canvas.Edge f) :
    (graph f).src (oldEdge f e)=.inl ((Canvas.graph f).src e) := by
  obtain ⟨i,e⟩:=e
  change placeMacroVertex f i ((FramedMacro.graph (canvasCell f i).shape).src
    (FramedMacro.oldEdge (canvasCell f i).shape e))=_
  rw [FramedMacro.old_source,place_oldVertex]
  rfl

theorem old_target (f : NumericFormula) (e : Canvas.Edge f) :
    (graph f).dst (oldEdge f e)=.inl ((Canvas.graph f).dst e) := by
  obtain ⟨i,e⟩:=e
  change placeMacroVertex f i ((FramedMacro.graph (canvasCell f i).shape).dst
    (FramedMacro.oldEdge (canvasCell f i).shape e))=_
  rw [FramedMacro.old_target,place_oldVertex]
  rfl

theorem oldDart_host (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    ((graph f).dartPair (oldDart f a)).1=.inl ((Canvas.graph f).dartPair a).1 := by
  obtain ⟨e,b⟩:=a
  cases b
  · exact old_target f e
  · exact old_source f e

theorem oldDart_injective (f : NumericFormula) : Function.Injective (oldDart f) := by
  intro a b h
  have hh:=congrArg (keepDart f) h
  simpa only [keepDart_oldDart,Option.some.injEq] using hh

theorem keepDart_eq_some_iff (f : NumericFormula) (d : Dart f)
    (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) : keepDart f d=some a ↔ oldDart f a=d := by
  constructor
  · intro h
    obtain ⟨e,b⟩:=d
    cases e with
    | inl e => cases h
    | inr e =>
      obtain ⟨i,e⟩:=e
      dsimp only [keepDart] at h
      split_ifs at h with hb
      · have hh:=Option.some.inj h
        subst a
        rfl
  · intro h
    rw [←h,keepDart_oldDart]

end PlanarHom.ColoringEmitter.FramedCanvas
