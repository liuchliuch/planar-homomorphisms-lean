import PlanarHom.RoutingIncidencePlanarity
import PlanarHom.ColoringTemplateBoundaryStates

/-! NEW literal Boolean variable/port decomposition of the canonical routing
canvas. Local auxiliaries are exactly the private suffix of each true template. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringCanvasBoolean
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate PositiveBlockProgram ColoringTemplateBoundaryStates

 def privateVariable (s : CellShape) (j : Fin s.auxiliaryCount) : Fin s.kind.variableCount :=
  ⟨s.portCount+j.val,by have:=j.isLt; have:=s.portCount_le; dsimp [CellShape.auxiliaryCount] at *; omega⟩

 theorem localBoolean_port (f:NumericFormula) (i:CanvasIndex f) (p:Fin (canvasCell f i).shape.portCount) :
    localBoolean f i ((canvasCell f i).shape.portVertex p)=.inl (boundaryPort f i p) := by
  simp [localBoolean,CellShape.portVertex,p.isLt]

 theorem localBoolean_private (f:NumericFormula) (i:CanvasIndex f) (j:Fin (canvasCell f i).shape.auxiliaryCount) :
    localBoolean f i (privateVariable (canvasCell f i).shape j)=.inr ⟨i,j⟩ := by
  simp only [localBoolean,privateVariable]
  rw [dif_neg (by omega)]
  congr 2
  apply Fin.ext
  simp

 def LocalAllowed (f:NumericFormula) (i:CanvasIndex f) (b:Fin (canvasCell f i).shape.portCount→Bool) : Prop :=
  Allowed (canvasCell f i).shape.kind.template (canvasCell f i).shape.portCount
    (canvasCell f i).shape.inputs_le_ports (canvasCell f i).shape.portCount_le b

 def localAssignment (f:NumericFormula) (a:BooleanGrid f→Bool) (i:CanvasIndex f) :
    Fin (canvasCell f i).shape.kind.variableCount→Bool := a ∘ localBoolean f i
 def localBoundary (f:NumericFormula) (b:Boundary f→Bool) (i:CanvasIndex f) :
    Fin (canvasCell f i).shape.portCount→Bool := b ∘ boundaryPort f i
 abbrev GridSolutions (f:NumericFormula) := {a:BooleanGrid f→Bool // ∀i,
    Satisfies (canvasCell f i).shape.kind.template.clauses (localAssignment f a i)}
 abbrev BoundarySolutions (f:NumericFormula) := {b:Boundary f→Bool // ∀i,LocalAllowed f i (localBoundary f b i)}

 theorem restrict_local (f:NumericFormula) (a:BooleanGrid f→Bool) (i:CanvasIndex f) :
    restrict (canvasCell f i).shape.kind.template (canvasCell f i).shape.portCount
      (canvasCell f i).shape.portCount_le (localAssignment f a i)=
      localBoundary f (fun b=>a (.inl b)) i := by
  funext p
  exact congrArg a (localBoolean_port f i p)

 def boundaryMap (f:NumericFormula) (a:GridSolutions f) : BoundarySolutions f :=
  ⟨fun b=>a.val (.inl b),by
    intro i
    have h:=(boundaryEquiv (canvasCell f i).shape.kind.template (canvasCell f i).shape.portCount
      (canvasCell f i).shape.inputs_le_ports (canvasCell f i).shape.portCount_le
      ⟨localAssignment f a.val i,a.property i⟩).property
    change Allowed _ _ _ _ (restrict _ _ _ (localAssignment f a.val i)) at h
    rw [restrict_local] at h
    exact h⟩

 def cellExtension (f:NumericFormula) (b:BoundarySolutions f) (i:CanvasIndex f) :
    Fin (canvasCell f i).shape.kind.variableCount→Bool :=
  (canvasCell f i).shape.kind.template.extend
    (input _ _ (canvasCell f i).shape.inputs_le_ports (localBoundary f b.val i))

 def complete (f:NumericFormula) (b:BoundarySolutions f) : BooleanGrid f→Bool :=
  Sum.elim b.val (fun q=>cellExtension f b q.1 (privateVariable (canvasCell f q.1).shape q.2))

 theorem complete_local (f:NumericFormula) (b:BoundarySolutions f) (i:CanvasIndex f) :
    localAssignment f (complete f b) i=cellExtension f b i := by
  funext v
  unfold localAssignment localBoolean
  dsimp only [Function.comp_apply]
  split
  · rename_i hv
    exact ((b.property i).2 ⟨v.val,hv⟩).symm
  · rename_i hv
    change cellExtension f b i (privateVariable (canvasCell f i).shape ⟨v.val-(canvasCell f i).shape.portCount,_⟩)=cellExtension f b i v
    apply congrArg (cellExtension f b i)
    apply Fin.ext
    dsimp [privateVariable]
    omega

 def completeSolution (f:NumericFormula) (b:BoundarySolutions f) : GridSolutions f :=
  ⟨complete f b,by
    intro i
    rw [complete_local]
    exact extension_satisfies _ _ (b.property i).1⟩

 theorem complete_boundaryMap (f:NumericFormula) (a:GridSolutions f) : completeSolution f (boundaryMap f a)=a := by
  apply Subtype.ext
  funext v
  cases v with
  | inl b => rfl
  | inr q =>
      let T:=(canvasCell f q.1).shape.kind.template
      let s:SourceSolutions T:=⟨localAssignment f a.val q.1,a.property q.1⟩
      have h:=congrArg Subtype.val ((boundaryEquiv T (canvasCell f q.1).shape.portCount
        (canvasCell f q.1).shape.inputs_le_ports (canvasCell f q.1).shape.portCount_le).symm_apply_apply s)
      change T.extend (input _ _ _ (restrict _ _ _ (localAssignment f a.val q.1)))=localAssignment f a.val q.1 at h
      rw [restrict_local] at h
      have hh:=congrFun h (privateVariable (canvasCell f q.1).shape q.2)
      change _=a.val (localBoolean f q.1 (privateVariable (canvasCell f q.1).shape q.2)) at hh
      rw [localBoolean_private] at hh
      exact hh

 def gridBoundaryEquiv (f:NumericFormula) : GridSolutions f ≃ BoundarySolutions f where
  toFun:=boundaryMap f
  invFun:=completeSolution f
  left_inv:=complete_boundaryMap f
  right_inv b:=rfl

end PlanarHom.ColoringCanvasBoolean
