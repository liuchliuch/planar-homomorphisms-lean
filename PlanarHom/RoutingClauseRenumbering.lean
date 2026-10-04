import PlanarHom.RoutingVariableRenumbering
import PlanarHom.ListBlockIndexing

/-! Exact occurrence-preserving index equivalence for the flattened emitted
clauses, including repeated equal clauses. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate

def Cell.clauses (c : Cell) : Formula ℕ := c.instruction.1.template.emit c.base (refs c.instruction)

theorem Cell.clauses_length (c : Cell) : c.clauses.length=c.shape.kind.clauseCount := by
  change (rename _ c.shape.kind.template.clauses).length=_
  rw [c.shape.kind.clauses_eq]
  simp [rename]

def Cell.numericClause (c : Cell) (j : Fin c.shape.kind.clauseCount) : Clause ℕ :=
  let v := c.shape.kind.clauseData j
  let r := c.instruction.1.template.translate c.base (refs c.instruction)
  (r v.1,r v.2.1,r v.2.2)

theorem Cell.clauses_get (c : Cell) (j : Fin c.shape.kind.clauseCount) :
    c.clauses.get (Fin.cast c.clauses_length.symm j)=c.numericClause j := by
  simp [Cell.clauses,Template.emit,Cell.instruction,c.shape.kind.clauses_eq,rename,List.map_ofFn,Cell.numericClause]

abbrev ClauseSlots (f : NumericFormula) := (i : CanvasIndex f) × Fin (canvasCell f i).shape.kind.clauseCount

def clauseAllocation (f : NumericFormula) (hf : NumericValid f) :
    ClauseSlots f ≃ Fin (PositiveRoutingCompiler.compile f).2.length :=
  (Equiv.sigmaCongrRight (fun i : CanvasIndex f => finCongr (canvasCell f i).clauses_length.symm)).trans
    ((ListBlockIndexing.equiv (canvas f) Cell.clauses).trans
      (finCongr (congrArg List.length (compile_clauses_eq_cells f hf).symm)))

private theorem get_cast {A : Type} {xs ys : List A} (h : xs=ys) (i : Fin xs.length) :
    ys.get (Fin.cast (congrArg List.length h) i)=xs.get i := by subst ys; rfl

/-- The numeric clause at the allocated position is literally the local
translated clause, not just an equal-sized or equisatisfiable replacement. -/
theorem clauseAllocation_get (f : NumericFormula) (hf : NumericValid f) (p : ClauseSlots f) :
    (PositiveRoutingCompiler.compile f).2.get (clauseAllocation f hf p)=
      (canvasCell f p.1).numericClause p.2 := by
  let q : (i : CanvasIndex f) × Fin (canvasCell f i).clauses.length :=
    ⟨p.1,Fin.cast (canvasCell f p.1).clauses_length.symm p.2⟩
  have hcast := get_cast (compile_clauses_eq_cells f hf).symm (ListBlockIndexing.equiv (canvas f) Cell.clauses q)
  have he := ListBlockIndexing.get_equiv (canvas f) Cell.clauses q
  exact hcast.trans (he.trans ((canvasCell f p.1).clauses_get p.2))

end PlanarHom.PositiveBlockProgram
