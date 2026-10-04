import PlanarHom.ColoringEmitterCanvas

/-! NEW exact registry-signal allocation. Initial signals and every cell's
real output ports enumerate the retained geometric registry bijectively. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open PositiveBlockProgram ParsimoniousNorOneInThree

abbrev SignalAllocation (f : NumericFormula) :=
  Fin f.1 ⊕ (i : Index f) × Fin (canvasCell f i).shape.outputCount

def sourceAllocation (f : NumericFormula) : SignalAllocation f → Allocated f
  | .inl i => .inl i
  | .inr p => .inr ⟨p.1,⟨p.2.val,by
      have h:=(canvasCell f p.1).shape.outputs_add_auxiliaries
      have hp:=p.2.isLt
      change p.2.val<(canvasCell f p.1).shape.kind.template.fresh
      omega⟩⟩

def allocatedSignal (f : NumericFormula) : SignalAllocation f → Signal f
  | .inl i => initialBoundary f i
  | .inr p => boundaryPort f p.1 ((canvasCell f p.1).freshPort p.2)

theorem sourceAllocation_injective (f : NumericFormula) : Function.Injective (sourceAllocation f) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj he)
    | inr b => cases he
  | inr a =>
    cases b with
    | inl b => cases he
    | inr b =>
      have hh:=Sum.inr.inj he
      have hi:=congrArg Sigma.fst hh
      have hv:=congrArg (fun p : (i : Index f) × Fin (canvasCell f i).fresh =>p.2.val) hh
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      dsimp [sourceAllocation] at hi hv
      subst j
      have hab:a=b := Fin.ext hv
      subst b
      rfl

theorem allocatedBool_sourceAllocation (f : NumericFormula) (a : SignalAllocation f) :
    allocatedBool f (sourceAllocation f a)=.inl (allocatedSignal f a) := by
  cases a with
  | inl i => rfl
  | inr p =>
    simp only [sourceAllocation,allocatedBool,dif_pos p.2.isLt,allocatedSignal]

theorem allocatedSignal_injective (f : NumericFormula) (hf : NumericValid f) :
    Function.Injective (allocatedSignal f) := by
  intro a b he
  apply sourceAllocation_injective f
  apply allocatedBool_injective f hf
  rw [allocatedBool_sourceAllocation,allocatedBool_sourceAllocation,he]

theorem allocatedSignal_surjective (f : NumericFormula) (hf : NumericValid f) :
    Function.Surjective (allocatedSignal f) := by
  intro b
  obtain ⟨a,ha⟩:=allocatedBool_surjective f hf (.inl b)
  cases a with
  | inl i => exact ⟨.inl i,Sum.inl.inj ha⟩
  | inr p =>
    by_cases hp:p.2.val<(canvasCell f p.1).shape.outputCount
    · refine ⟨.inr ⟨p.1,⟨p.2.val,hp⟩⟩,?_⟩
      exact Sum.inl.inj (by simpa only [allocatedBool,dif_pos hp] using ha)
    · simp only [allocatedBool,dif_neg hp] at ha
      cases ha

def signalEquiv (f : NumericFormula) (hf : NumericValid f) : SignalAllocation f ≃ Signal f :=
  Equiv.ofBijective (allocatedSignal f) ⟨allocatedSignal_injective f hf,allocatedSignal_surjective f hf⟩

@[simp] theorem signalEquiv_initial (f : NumericFormula) (hf : NumericValid f) (i : Fin f.1) :
    signalEquiv f hf (.inl i)=initialBoundary f i := rfl
@[simp] theorem signalEquiv_output (f : NumericFormula) (hf : NumericValid f)
    (i : Index f) (p : Fin (canvasCell f i).shape.outputCount) :
    signalEquiv f hf (.inr ⟨i,p⟩)=boundaryPort f i ((canvasCell f i).freshPort p) := rfl

end PlanarHom.ColoringEmitter.Canvas
