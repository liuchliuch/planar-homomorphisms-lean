import PlanarHom.ColoringCanvasBooleanGrid

/-! NEW exact Boolean boundary-assignment/source-solution bijection for the
actual routing canvas, using its proved variable allocation and literal emitted
clause identity. Empty formulas retain all declared independent input bits. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringCanvasBoolean
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate PositiveBlockProgram CountingCookLevin
variable (f:NumericFormula) (hf:NumericValid f)

 theorem variable_inverse_name (v:BooleanGrid f) :
    ((variableEquiv f hf).symm v).val=booleanName f hf v := by
  have hh:=variableEquiv_name f hf ((variableEquiv f hf).symm v)
  simpa only [Equiv.apply_symm_apply] using hh.symm

 theorem translated_read (w:Fin (PositiveRoutingCompiler.compile f).1→Bool) (i:CanvasIndex f)
    (v:Fin (canvasCell f i).shape.kind.variableCount) :
    readBit (List.ofFn w) ((canvasCell f i).instruction.1.template.translate
      (canvasCell f i).base (refs (canvasCell f i).instruction) v)=
      (w ∘ (variableEquiv f hf).symm) (localBoolean f i v) := by
  rw [←localBoolean_name f hf,←variable_inverse_name f hf]
  simp [readBit]

 theorem satisfies_flatMap {A B : Type} (xs:List A) (cs:A→Formula B) (a:B→Bool) :
    Satisfies (xs.flatMap cs) a ↔ ∀x∈xs,Satisfies (cs x) a := by
  constructor
  · intro h x hx c hc
    exact h c (List.mem_flatMap.mpr ⟨x,hx,hc⟩)
  · intro h c hc
    obtain ⟨x,hx,hc⟩:=List.mem_flatMap.mp hc
    exact h x hx c hc

 theorem cell_satisfaction_iff (w:Fin (PositiveRoutingCompiler.compile f).1→Bool) (i:CanvasIndex f) :
    Satisfies ((canvasCell f i).instruction.1.template.emit (canvasCell f i).base
      (refs (canvasCell f i).instruction)) (readBit (List.ofFn w)) ↔
    Satisfies (canvasCell f i).shape.kind.template.clauses
      (localAssignment f (w ∘ (variableEquiv f hf).symm) i) := by
  rw [Template.emit,satisfies_rename]
  have he:(readBit (List.ofFn w) ∘ (canvasCell f i).instruction.1.template.translate
      (canvasCell f i).base (refs (canvasCell f i).instruction))=
      localAssignment f (w ∘ (variableEquiv f hf).symm) i := by
    funext v
    exact translated_read f hf w i v
  rw [he]
  rfl

 theorem numeric_satisfaction_iff (w:Fin (PositiveRoutingCompiler.compile f).1→Bool) :
    Satisfies (PositiveRoutingCompiler.compile f).2 (readBit (List.ofFn w)) ↔
      ∀i,Satisfies (canvasCell f i).shape.kind.template.clauses
        (localAssignment f (w ∘ (variableEquiv f hf).symm) i) := by
  rw [compile_clauses_eq_cells f hf,satisfies_flatMap]
  constructor
  · intro h i
    exact (cell_satisfaction_iff f hf w i).mp (h _ (List.get_mem _ _))
  · intro h c hc
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hc
    exact (cell_satisfaction_iff f hf w i).mpr (h i)

 def numericGridEquiv : NorExactOne.Solutions (PositiveRoutingCompiler.compile f) ≃ GridSolutions f where
  toFun a:=⟨a.val ∘ (variableEquiv f hf).symm,(numeric_satisfaction_iff f hf a.val).mp a.property⟩
  invFun a:=⟨a.val ∘ variableEquiv f hf,(numeric_satisfaction_iff f hf _).mpr (by
    intro i
    have he:(a.val ∘ variableEquiv f hf) ∘ (variableEquiv f hf).symm=a.val := by
      funext v
      simp only [Function.comp_apply,Equiv.apply_symm_apply]
    rw [he]
    exact a.property i)⟩
  left_inv a:=by
    apply Subtype.ext
    funext v
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  right_inv a:=by
    apply Subtype.ext
    funext v
    simp only [Function.comp_apply,Equiv.apply_symm_apply]

 def sourceBoundaryEquiv : NorExactOne.Solutions f ≃ BoundarySolutions f :=
  (PositiveRoutingCompiler.solutionsEquiv f hf).trans ((numericGridEquiv f hf).trans (gridBoundaryEquiv f))

include hf

 theorem boundary_count : Nat.card (BoundarySolutions f)=Nat.card (NorExactOne.Solutions f) :=
  (Nat.card_congr (sourceBoundaryEquiv f hf)).symm

 theorem boundary_count_empty (hnil:f.2=[]) : Nat.card (BoundarySolutions f)=2^f.1 := by
  rw [boundary_count f hf]
  simp [NorExactOne.Solutions,hnil,Satisfies,Nat.card_eq_fintype_card]

end PlanarHom.ColoringCanvasBoolean
