import PlanarHom.ColoringEmitterInputAllocation
import PlanarHom.ColoringCanvasFrontierComplete

/-! NEW literal input origins in the canonical signal registry. Every input
is original or comes from a strictly earlier emitted cell. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem leftPort_input (s : CellShape) (p : Fin s.portCount) (hp:p∈s.leftPorts) :
     p.val<Macro.inputCount s.kind := by
   cases s <;> fin_cases p <;> simp [CellShape.leftPorts,CellShape.kind,Macro.inputCount] at hp ⊢

 theorem cellBase_mono (f : NumericFormula) (hf:NumericValid f) (i j : Index f) (hij:i.val≤j.val) :
     (canvasCell f i).base≤(canvasCell f j).base := by
   rcases eq_or_lt_of_le hij with he|hl
   · have h:i=j:=Fin.ext he
     simp [h]
   · have h:=List.pairwise_iff_get.mp (baseSequence_ordered (canvas f) f.1 (canvas_bases f hf)) i j hl
     change (canvasCell f i).base+(canvasCell f i).fresh≤(canvasCell f j).base at h
     omega

 theorem input_origin (f : NumericFormula) (hf:NumericValid f) (i : Index f)
     (p : Fin (canvasCell f i).shape.portCount) (hp:p∈(canvasCell f i).shape.leftPorts) :
     (∃a:Fin f.1,(signalEquiv f hf).symm (boundaryPort f i p)=.inl a) ∨
     ∃(j:Index f) (o:Fin (canvasCell f j).shape.outputCount),
       j.val < i.val ∧ (signalEquiv f hf).symm (boundaryPort f i p)=.inr ⟨j,o⟩ := by
   generalize ha:(signalEquiv f hf).symm (boundaryPort f i p)=a
   cases a with
   | inl a => exact Or.inl ⟨a,rfl⟩
   | inr a =>
     rcases a with ⟨j,o⟩
     right
     refine ⟨j,o,?_,rfl⟩
     have hs : boundaryPort f i p=boundaryPort f j ((canvasCell f j).freshPort o) := by
       have h:=congrArg (signalEquiv f hf) ha
       simpa only [Equiv.apply_symm_apply,signalEquiv_output] using h
     have hn:=congrArg (boundaryName f hf) hs
     rw [boundaryName_port,boundaryName_port,Cell.freshPort_reference,
       cell_port_input _ _ (leftPort_input _ _ hp)] at hn
     have hb:=cell_input_lt f hf i p.val (leftPort_input _ _ hp)
     by_contra hlt
     have hm:=cellBase_mono f hf i j (by omega)
     omega

end PlanarHom.ColoringEmitter.Canvas
