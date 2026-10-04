import PlanarHom.ColoringEmitterPrefixAllocation

/-! NEW source-reference bounds and exact dictionary persistence at every
literal cell occurrence of the valid routing canvas. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram ParsimoniousNorOneInThree

theorem inputCount_eq (k : Kind) : Macro.inputCount k=k.template.inputs := by cases k <;> decide

theorem refs_eq_inputRef (op : Instruction) (i : Fin op.1.template.inputs) :
    refs op i=inputRef op i.val := by
  rcases op with ⟨k,a,b,c⟩
  cases k <;> fin_cases i <;> rfl

theorem cell_port_input (c : Cell) (p : Fin c.shape.portCount)
    (hp:p.val<Macro.inputCount c.shape.kind) :
    (c.portData p).1=inputRef c.instruction p.val := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases p <;>
    simp [Cell.portData,Cell.instruction,CellShape.kind,Macro.inputCount,inputRef] at hp ⊢

theorem cell_port_output (c : Cell) (p : Fin c.shape.portCount)
    (hp:¬p.val<Macro.inputCount c.shape.kind) :
    (c.portData p).1=c.base+(p.val-Macro.inputCount c.shape.kind) := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases p <;>
    simp [Cell.portData,Cell.instruction,CellShape.kind,Macro.inputCount,inputRef] at hp ⊢

theorem baseSequence_input_lt (cs : List Cell) (m : ℕ)
    (hb:BaseSequence m cs) (hv:PositiveBlockProgram.Valid m (cs.map Cell.instruction))
    (i : Fin cs.length) (j : Fin (cs.get i).instruction.1.template.inputs) :
    inputRef (cs.get i).instruction j.val<(cs.get i).base := by
  induction cs generalizing m with
  | nil => exact i.elim0
  | cons c cs ih =>
    cases i using Fin.cases with
    | zero =>
      change inputRef c.instruction j.val<c.base
      rw [←refs_eq_inputRef,hb.1]
      exact hv.1 j
    | succ i => exact ih (m+c.fresh) hb.2 hv.2 i j

namespace Canvas
 theorem state_eq_before (f : NumericFormula) (i : Index f) :
    state f=(((canvas f).drop i.val).map Cell.instruction).foldl ColoringEmitter.step (before f i) := by
  have hlist:canvas f=(canvas f).take i.val++(canvas f).drop i.val :=
    (List.take_append_drop _ _).symm
  have hfold:=congrArg (fun cs : List Cell=>(cs.map Cell.instruction).foldl ColoringEmitter.step (initial f.1)) hlist
  rw [state_eq_cells]
  simpa only [List.map_append,List.foldl_append,before] using hfold

 theorem state_dictionary_before (f : NumericFormula) (i : Index f) (j : ℕ)
     (hj:j<(before f i).dictionary.length) :
     (state f).dictionary[j]?.getD 0=(before f i).dictionary[j]?.getD 0 := by
   rw [state_eq_before,fold_dictionary_old _ _ _ hj]

 theorem cell_input_lt (f : NumericFormula) (hf:NumericValid f) (i : Index f)
     (j : ℕ) (hj:j<Macro.inputCount (canvasCell f i).shape.kind) :
     inputRef (canvasCell f i).instruction j<(canvasCell f i).base := by
   have hvalid : PositiveBlockProgram.Valid f.1 ((canvas f).map Cell.instruction) := by
     rw [canvas_erase]
     exact PositiveRoutingCompiler.program_valid f hf
   exact baseSequence_input_lt (canvas f) f.1 (canvas_bases f hf) hvalid i
     ⟨j,by simpa only [Cell.instruction,←inputCount_eq] using hj⟩
end Canvas
end PlanarHom.ColoringEmitter
