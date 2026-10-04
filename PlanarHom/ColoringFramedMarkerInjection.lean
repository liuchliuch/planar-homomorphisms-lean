import PlanarHom.ColoringFramedSpliceProgram
import PlanarHom.ColoringCanvasRotationRows
import PlanarHom.ColoringCanvasInputOrigins

/-! NEW actual injective marker allocation on the canonical framed occurrence
carrier. All local closing-vertex separation is checked on the literal tables. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization

namespace FramedMacro

 def boundaryVertex (s:CellShape) : Fin (leftCount s)⊕Fin (rightCount s)→Fin (vertexCount s) :=
  Sum.elim (leftVertex s) (rightVertex s)

 theorem boundaryVertex_injective (s:CellShape) : Function.Injective (boundaryVertex s) := by
  cases s <;> decide +kernel

 theorem portClosing_host (s:CellShape) (p:LocalPatch.Port s) :
    ((graph s).dartPair (portClosing s p)).1=boundaryVertex s ((portEquiv s).symm p) := by
  unfold portClosing boundaryVertex
  cases (portEquiv s).symm p with
  | inl i => exact left_host s i
  | inr i => exact right_host s i

 theorem portClosing_injective (s:CellShape) : Function.Injective (portClosing s) := by
  intro p q h
  apply (portEquiv s).symm.injective
  apply boundaryVertex_injective s
  rw [←portClosing_host,←portClosing_host,h]

 theorem leftPort_injective (s:CellShape) : Function.Injective (leftPort s) := by
  intro i j h
  exact Sum.inl.inj ((portEquiv s).injective h)

 theorem leftClosing_injective (s:CellShape) : Function.Injective (leftClosing s) := by
  intro i j h
  apply leftPort_injective s
  apply portClosing_injective s
  simpa only [portClosing_left] using h

 theorem leftPort_mem (s:CellShape) (i:Fin (leftCount s)) : (leftPort s i).1∈s.leftPorts := by
  cases s <;> fin_cases i <;> decide

end FramedMacro
namespace FramedCanvas

 theorem seedDart_injective (f:NumericFormula) : Function.Injective (seedDart f) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (congrArg (fun a:Dart f=>a.2) h)

 theorem patchDart_injective (f:NumericFormula) (i:Canvas.Index f) : Function.Injective (patchDart f i) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he:a=c:=by
    simpa only [patchDart,Prod.mk.injEq,Sum.inr.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using congrArg Prod.fst h
  exact Prod.ext he (congrArg (fun a:Dart f=>a.2) h)

 theorem initialVertex_injective (f:NumericFormula) :
    Function.Injective (fun p:Fin f.1×Fin 3=>initialVertex f p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hh:=congrArg Fin.val h
  have ha:=a.isLt
  have hb:=b.isLt
  change 3*i.val+(2-a.val)=3*j.val+(2-b.val) at hh
  apply Prod.ext
  · apply Fin.ext
    change i.val=j.val
    omega
  · apply Fin.ext
    change a.val=b.val
    omega

 def allocationMarker (f:NumericFormula) : Canvas.SignalAllocation f×Fin 3→Dart f
  | (.inl i,b)=>seedDart f ((finRotate (3*f.1)).symm (initialVertex f i b),true)
  | (.inr ⟨i,o⟩,b)=>patchDart f i (reversePerm _
      (FramedMacro.portClosing (canvasCell f i).shape ((canvasCell f i).freshPort o,b)))

 theorem allocationMarker_injective (f:NumericFormula) : Function.Injective (allocationMarker f) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases a with
  | inl a =>
    cases c with
    | inl c =>
      have hh:initialVertex f a b=initialVertex f c d:=
        (finRotate (3*f.1)).symm.injective (congrArg Prod.fst (seedDart_injective f h))
      have he:(a,b)=(c,d):=initialVertex_injective f hh
      exact Prod.ext (congrArg Sum.inl (congrArg Prod.fst he)) (congrArg (fun p:Fin f.1×Fin 3=>p.2) he)
    | inr c => exact False.elim (Sum.inl_ne_inr (congrArg Prod.fst h))
  | inr a =>
    cases c with
    | inl c => exact False.elim (Sum.inr_ne_inl (congrArg Prod.fst h))
    | inr c =>
      rcases a with ⟨i,a⟩
      rcases c with ⟨j,c⟩
      have hij:i=j:=congrArg Sigma.fst (Sum.inr.inj (congrArg Prod.fst h))
      subst j
      have hp:=FramedMacro.portClosing_injective (canvasCell f i).shape
        ((reversePerm _).injective (patchDart_injective f i h))
      have hpv:=congrArg (fun p:LocalPatch.Port (canvasCell f i).shape=>p.1.val) hp
      have hac:a=c:=by
        apply Fin.ext
        dsimp only [Cell.freshPort] at hpv
        omega
      subst c
      exact Prod.ext rfl (congrArg (fun p:LocalPatch.Port (canvasCell f i).shape=>p.2) hp)

 theorem producerMarker_injective (f:NumericFormula) (hf:NumericValid f) :
    Function.Injective (producerMarker f hf) := by
  intro a b h
  have heq (b:Canvas.BoundaryTriple f): producerMarker f hf b=allocationMarker f ((Canvas.signalEquiv f hf).symm b.1,b.2):=by
    unfold producerMarker allocationMarker
    cases (Canvas.signalEquiv f hf).symm b.1 <;> rfl
  rw [heq,heq] at h
  have he:((Canvas.signalEquiv f hf).symm a.1,a.2)=((Canvas.signalEquiv f hf).symm b.1,b.2):=
    allocationMarker_injective f h
  exact Prod.ext ((Canvas.signalEquiv f hf).symm.injective (congrArg Prod.fst he)) (congrArg (fun p:Canvas.SignalAllocation f×Fin 3=>p.2) he)

 theorem oldMarker_injective (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    Function.Injective (oldMarker f hf i) := by
  intro a b h
  exact (sharedIndex f i).injective (FramedMacro.leftPort_injective _
    (Canvas.port_injective f i (producerMarker_injective f hf h)))

 theorem newMarker_injective (f:NumericFormula) (i:Canvas.Index f) :
    Function.Injective (newMarker f i) := by
  intro a b h
  exact (sharedIndex f i).injective (FramedMacro.leftClosing_injective _
    ((reversePerm _).injective (patchDart_injective f i h)))

end FramedCanvas
end PlanarHom.ColoringEmitter
