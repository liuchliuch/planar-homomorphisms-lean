import PlanarHom.ColoringEmitterSignalAllocation
import PlanarHom.ListBlockIndexing

/-! NEW exact numeric prefix allocation for every original cell occurrence. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram ParsimoniousNorOneInThree

theorem fold_vertices (ops : List Instruction) (s : State) :
    (ops.foldl step s).vertices=s.vertices+(ops.map (fun op=>Macro.addedVertices op.1)).sum := by
  induction ops generalizing s with
  | nil => simp
  | cons op ops ih => simp [List.foldl_cons,ih,step,Nat.add_assoc]

theorem run_vertices (n : ℕ) (ops : List Instruction) :
    (run n ops).vertices=3*n+(ops.map (fun op=>Macro.addedVertices op.1)).sum := fold_vertices ops (initial n)

theorem fold_dictionary_old (ops : List Instruction) (s : State) (i : ℕ)
    (hi:i<s.dictionary.length) :
    (ops.foldl step s).dictionary[i]?.getD 0=s.dictionary[i]?.getD 0 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldl_cons,ih (step s op) (by simp [step]; omega),step_dictionary_old s op i hi]

theorem take_succ_get {A : Type} (xs : List A) (i : Fin xs.length) :
    xs.take (i.val+1)=xs.take i.val++[xs.get i] := by
  induction xs with
  | nil => exact i.elim0
  | cons a xs ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [Fin.val_succ,List.take_succ_cons,List.get_cons_succ,List.cons_append] using congrArg (List.cons a) (ih i)

theorem baseSequence_get (cs : List Cell) (m : ℕ) (h:BaseSequence m cs) (i : Fin cs.length) :
    (cs.get i).base=width m ((cs.take i.val).map Cell.instruction) := by
  induction cs generalizing m with
  | nil => exact i.elim0
  | cons c cs ih =>
    cases i using Fin.cases with
    | zero => simpa [width] using h.1
    | succ i =>
      simpa only [Fin.val_succ,List.get_cons_succ,List.take_succ_cons,List.map_cons,width,Cell.fresh] using
        ih (m+c.fresh) h.2 i

namespace Canvas

def state (f : NumericFormula) : State := run f.1 (PositiveRoutingCompiler.program f)
def before (f : NumericFormula) (i : Index f) : State :=
  (((canvas f).take i.val).map Cell.instruction).foldl step (initial f.1)
def after (f : NumericFormula) (i : Index f) : State := step (before f i) (canvasCell f i).instruction

 theorem state_eq_cells (f : NumericFormula) : state f=((canvas f).map Cell.instruction).foldl step (initial f.1) := by
  rw [canvas_erase]
  rfl

 theorem before_source (f : NumericFormula) (hf:NumericValid f) (i : Index f) :
    (before f i).sourceBase=(canvasCell f i).base := by
  rw [before,fold_sourceBase]
  exact (baseSequence_get (canvas f) f.1 (canvas_bases f hf) i).symm

 theorem before_dictionary_length (f : NumericFormula) (hf:NumericValid f) (i : Index f) :
    (before f i).dictionary.length=(canvasCell f i).base := by
  rw [←before_source f hf i]
  exact fold_dictionary_length _ _ (by simp [initial])

 theorem before_vertices (f : NumericFormula) (i : Index f) :
    (before f i).vertices=3*f.1+(((canvas f).take i.val).map (fun c=>Macro.addedVertices c.shape.kind)).sum := by
  rw [before,fold_vertices]
  simp only [initial,List.map_map,Cell.instruction,Function.comp_def]

 theorem state_eq_after (f : NumericFormula) (i : Index f) :
    state f=(((canvas f).drop (i.val+1)).map Cell.instruction).foldl step (after f i) := by
  have hlist : canvas f=(canvas f).take i.val++[canvasCell f i]++(canvas f).drop (i.val+1) := by
    calc
      canvas f=(canvas f).take (i.val+1)++(canvas f).drop (i.val+1) :=
        (List.take_append_drop _ _).symm
      _ = _ := by rw [take_succ_get]; rfl
  have hfold:=congrArg (fun cs : List Cell=>(cs.map Cell.instruction).foldl step (initial f.1)) hlist
  rw [state_eq_cells]
  simpa only [List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,before,after] using hfold

 theorem before_valid (f : NumericFormula) (i : Index f) : (before f i).Valid :=
  fold_valid _ _ (initial_valid _)

 abbrev Allocation (f : NumericFormula) :=
   Fin (3*f.1) ⊕ (i : Index f) × Fin (Macro.addedVertices (canvasCell f i).shape.kind)

 theorem state_vertices_sum (f : NumericFormula) :
     (state f).vertices=3*f.1+∑i:Index f,Macro.addedVertices (canvasCell f i).shape.kind := by
   rw [state,run_vertices,←canvas_erase,List.map_map]
   change 3*f.1+((canvas f).map (fun c=>Macro.addedVertices c.shape.kind)).sum=
     3*f.1+∑i:Index f,Macro.addedVertices ((canvas f).get i).shape.kind
   exact congrArg (fun n=>3*f.1+n) (sum_get (canvas f) (fun c=>Macro.addedVertices c.shape.kind)).symm

 def allocationIndex (f : NumericFormula) : Allocation f ≃ Fin (state f).vertices :=
   (Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans
     (finSumFinEquiv.trans (finCongr (state_vertices_sum f).symm))

 @[simp] theorem allocationIndex_initial (f : NumericFormula) (i : Fin (3*f.1)) :
     (allocationIndex f (.inl i)).val=i.val := rfl

 theorem prefix_sum (f : NumericFormula) (i : Index f) :
     (∑j:Fin i.val,Macro.addedVertices (canvasCell f (Fin.castLE i.isLt.le j)).shape.kind)=
       (((canvas f).take i.val).map (fun c=>Macro.addedVertices c.shape.kind)).sum := by
   have h:=ListBlockIndexing.prefix_length (canvas f) (fun c=>List.range (Macro.addedVertices c.shape.kind)) i
   simpa using h

 @[simp] theorem allocationIndex_new (f : NumericFormula) (i : Index f)
     (j : Fin (Macro.addedVertices (canvasCell f i).shape.kind)) :
     (allocationIndex f (.inr ⟨i,j⟩)).val=(before f i).vertices+j.val := by
   simp only [allocationIndex,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.refl_apply,
     finCongr_apply,Fin.coe_cast,Sum.map_inr,finSumFinEquiv_apply_right,Fin.coe_natAdd,finSigmaFinEquiv_apply]
   change 3*f.1+((∑z:Fin i.val,Macro.addedVertices (canvasCell f (Fin.castLE i.isLt.le z)).shape.kind)+j.val)=_
   rw [prefix_sum,before_vertices]
   omega

 theorem state_dictionary_initial (f : NumericFormula) (i : Fin f.1) :
     (state f).dictionary[i.val]?.getD 0=3*i.val := by
   rw [state,run,fold_dictionary_old _ _ _ (by simpa [initial] using i.isLt)]
   exact initial_dictionary_get f.1 i.val i.isLt

 theorem state_dictionary_output (f : NumericFormula) (hf:NumericValid f) (i : Index f)
     (j : Fin (canvasCell f i).shape.outputCount) :
     (state f).dictionary[(canvasCell f i).base+j.val]?.getD 0=(before f i).vertices+3*j.val := by
   have hlen:=before_dictionary_length f hf i
   have hsource:=before_source f hf i
   have hshape : ∀s:CellShape,s.outputCount=Macro.outputCount s.kind := by intro s; cases s <;> decide
   have hout : j.val<Macro.outputCount (canvasCell f i).instruction.1 := by
     simpa only [Cell.instruction,←hshape] using j.isLt
   have hfresh : j.val<(canvasCell f i).instruction.1.template.fresh := by
     have h:=(canvasCell f i).shape.outputs_add_auxiliaries
     change j.val<(canvasCell f i).shape.kind.template.fresh
     omega
   have hidx : (canvasCell f i).base+j.val<(after f i).dictionary.length := by
     simp only [after,step,List.length_append,freshDictionary,List.length_map,List.length_range,hlen]
     omega
   rw [state_eq_after f i,fold_dictionary_old _ _ _ hidx]
   have h:=step_dictionary_new (before f i) (canvasCell f i).instruction j.val
     (by rw [hlen,hsource]) hfresh
   simpa only [after,hsource,if_pos hout] using h

end Canvas
end PlanarHom.ColoringEmitter
