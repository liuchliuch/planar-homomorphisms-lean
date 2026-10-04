import PlanarHom.RoutingMachinePrimitives
import PlanarHom.RestrictedListFoldMachines

/-! Honest serialization of a whole materialized block program. Every gate
appends its actual clauses and increases the actual unary variable header. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity ParsimoniousNorOneInThree ParsimoniousBlockTemplate
open PairProjectionMachines ArithmeticCircuitPrimitives

def formulaStep (f : NumericFormula) (op : Instruction) : NumericFormula :=
  op.1.template.append (f,refs op)

theorem fp_refs (k : Kind) : FP referenceEncoding (BitEncoding.nat.vector k.template.inputs)
    (fun r => refs (k,r)) := by
  have hx := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hyz := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hy := hyz.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hz := hyz.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  apply FixedVectorMachines.fp_assemble
  cases k <;> intro i <;> fin_cases i <;> first | exact hx | exact hy | exact hz

theorem fp_appendKind (k : Kind) : FP (formulaEncoding.prod referenceEncoding) formulaEncoding
    (fun p => formulaStep p.1 (k,p.2)) :=
  ((fp_fst formulaEncoding referenceEncoding).pair
    ((fp_snd formulaEncoding referenceEncoding).comp (fp_refs k))).comp k.template.fp_append

theorem fp_formulaStep : FP (formulaEncoding.prod instructionEncoding) formulaEncoding
    (fun p => formulaStep p.1 p.2) := by
  have hf := fp_fst formulaEncoding instructionEncoding
  have hop := fp_snd formulaEncoding instructionEncoding
  have hk := (hop.comp (fp_fst kindEncoding referenceEncoding)).comp fp_kindCode
  have hhi := hk.comp (fp_fst BitEncoding.bool BitEncoding.bool)
  have hlo := hk.comp (fp_snd BitEncoding.bool BitEncoding.bool)
  have hr := hop.comp (fp_snd kindEncoding referenceEncoding)
  have hp := hf.pair hr
  have hfalse := (hlo.pair ((hp.comp (fp_appendKind .cross)).pair (hp.comp (fp_appendKind .wire)))).comp (ConditionalMachines.fp_select formulaEncoding)
  have htrue := (hlo.pair ((hp.comp (fp_appendKind .test)).pair (hp.comp (fp_appendKind .fan)))).comp (ConditionalMachines.fp_select formulaEncoding)
  exact ((hhi.pair (htrue.pair hfalse)).comp (ConditionalMachines.fp_select formulaEncoding)).congr (fun p => by rcases p with ⟨f,k,r⟩; cases k <;> rfl)

theorem fold_formulaStep (ops : List Instruction) (f : NumericFormula) :
    ops.foldl formulaStep f=(width f.1 ops,f.2++network f.1 ops) := by
  induction ops generalizing f with
  | nil => simp [width,network]
  | cons op ops ih =>
    rw [List.foldl_cons,ih]
    simp [formulaStep,Template.append,width,network,List.append_assoc]

theorem Kind.fresh_le (k : Kind) : k.template.fresh≤15 := by cases k <;> decide

theorem Kind.clauses_le (k : Kind) : k.template.clauses.length≤12 := by cases k <;> decide

theorem network_length_bound (ops : List Instruction) (m : ℕ) : (network m ops).length≤12*ops.length := by
  induction ops generalizing m with
  | nil => simp [network]
  | cons op ops ih =>
    have ht := op.1.clauses_le
    have hh := ih (m+op.1.template.fresh)
    simp only [network,List.length_append,Template.emit,rename,List.length_map,List.length_cons]
    omega

def Instruction.CodeBound (B : ℕ) (op : Instruction) : Prop :=
  (BitEncoding.nat.encode op.2.1).length≤B ∧
  (BitEncoding.nat.encode op.2.2.1).length≤B ∧ (BitEncoding.nat.encode op.2.2.2).length≤B

theorem refs_code_bound (op : Instruction) (B : ℕ) (h : op.CodeBound B)
    (i : Fin op.1.template.inputs) : (BitEncoding.nat.encode (refs op i)).length≤B := by
  rcases op with ⟨k,r⟩
  cases k <;> fin_cases i <;> first | exact h.1 | exact h.2.1 | exact h.2.2

theorem translate_code_bound (op : Instruction) (m B : ℕ) (h : op.CodeBound B)
    (v : Fin (op.1.template.inputs+op.1.template.fresh)) :
    (BitEncoding.nat.encode (op.1.template.translate m (refs op) v)).length≤m+15+B := by
  by_cases hv : v.val<op.1.template.inputs
  · simp only [Template.translate,dif_pos hv]
    exact (refs_code_bound op B h ⟨v.val,hv⟩).trans (by omega)
  · simp only [Template.translate,dif_neg hv]
    have hlen := Complexity.encodeNat_length_le (m+(v.val-op.1.template.inputs))
    have hfr := op.1.fresh_le
    omega

theorem emit_clause_code_bound (op : Instruction) (m B : ℕ) (h : op.CodeBound B)
    (c : Clause ℕ) (hc : c∈op.1.template.emit m (refs op)) :
    (clauseEncoding.encode c).length≤5*(m+15+B)+2 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
  have h1 := translate_code_bound op m B h v.1
  have h2 := translate_code_bound op m B h v.2.1
  have h3 := translate_code_bound op m B h v.2.2
  simp only [clauseEncoding,BitEncoding.prod_length]
  omega

theorem network_clause_code_bound (ops : List Instruction) (m B : ℕ)
    (h : ∀op∈ops,op.CodeBound B) (c : Clause ℕ) (hc : c∈network m ops) :
    (clauseEncoding.encode c).length≤5*(m+15*ops.length+B)+2 := by
  induction ops generalizing m with
  | nil => simp [network] at hc
  | cons op ops ih =>
    rcases List.mem_append.mp hc with hc | hc
    · have hb := emit_clause_code_bound op m B (h op (by simp)) c hc
      simp only [List.length_cons]
      omega
    · have hb := ih (m+op.1.template.fresh) (fun q hq => h q (by simp [hq])) hc
      have hf := op.1.fresh_le
      simp only [List.length_cons]
      omega

def blockSeedEncoding : BitEncoding (ℕ × List Instruction) :=
  (formulaEncoding.prod instructionEncoding.list).retract
    (fun p => ((p.1,[]),p.2)) (fun p => (p.1.1,p.2)) (by intro p; rfl)

theorem instruction_bound_input (p : ℕ × List Instruction) (op : Instruction) (hop : op∈p.2) :
    op.CodeBound (blockSeedEncoding.encode p).length := by
  have h := ListMapMachines.mem_le_sum_map (fun q => (instructionEncoding.encode q).length) hop
  have he : (instructionEncoding.list.encode p.2).length=
      2*(BitEncoding.nat.encode p.2.length).length+1+
      2*(p.2.map (fun q => (instructionEncoding.encode q).length)).sum+p.2.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hp : (blockSeedEncoding.encode p).length=
      2*(formulaEncoding.encode (p.1,[])).length+(instructionEncoding.list.encode p.2).length+1 := by
    simp [blockSeedEncoding,BitEncoding.retract,BitEncoding.prod_length]
  dsimp only at h
  simp only [Instruction.CodeBound]
  have hoplen : (instructionEncoding.encode op).length≤(blockSeedEncoding.encode p).length := by omega
  simp only [instructionEncoding,referenceEncoding,BitEncoding.prod_length] at hoplen
  omega

theorem block_prefix_size (p : ℕ × List Instruction) (i : ℕ) (_hi : i≤p.2.length) :
    (formulaEncoding.encode ((p.2.take i).foldl formulaStep (p.1,[]))).length≤
      (Polynomial.C 10000*(Polynomial.X+1)^2).eval (blockSeedEncoding.encode p).length := by
  let N := (blockSeedEncoding.encode p).length
  let ops := p.2.take i
  have he : N=2*(2*p.1+(clauseEncoding.list.encode []).length+1)+(instructionEncoding.list.encode p.2).length+1 := by
    simp [N,blockSeedEncoding,BitEncoding.retract,formulaEncoding,BitEncoding.prod_length]
  have hn : p.1≤N := by omega
  have hl := instructionEncoding.list_length_le p.2
  have hk : ops.length≤N := by dsimp [ops]; simp only [List.length_take]; omega
  have hbound : ∀op∈ops,op.CodeBound N := fun op hop =>
    instruction_bound_input p op (List.mem_of_mem_take hop)
  have hc := network_length_bound ops p.1
  have hs := List.sum_le_card_nsmul ((network p.1 ops).map (fun c => (clauseEncoding.encode c).length))
      (5*(p.1+15*ops.length+N)+2) (by
    intro v hv
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
    exact network_clause_code_bound ops p.1 N hbound c hc)
  simp only [List.length_map,smul_eq_mul] at hs
  have hhead := Complexity.encodeNat_length_le (network p.1 ops).length
  have hlist : (clauseEncoding.list.encode (network p.1 ops)).length=
      2*(BitEncoding.nat.encode (network p.1 ops).length).length+1+
      2*((network p.1 ops).map (fun c => (clauseEncoding.encode c).length)).sum+(network p.1 ops).length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hwidth : width p.1 ops≤p.1+15*ops.length := width_bound _ _
  rw [fold_formulaStep]
  simp only [List.nil_append,formulaEncoding,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  change 2*width p.1 ops+(clauseEncoding.list.encode (network p.1 ops)).length+1≤
    (Polynomial.C 10000*(Polynomial.X+1)^2).eval N
  rw [hlist]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  have hp := Nat.mul_le_mul (hc.trans (Nat.mul_le_mul_left 12 hk))
    (show 5*(p.1+15*ops.length+N)+2≤85*N+2 by omega)
  nlinarith

theorem fp_blockFold : FP blockSeedEncoding formulaEncoding
    (fun p => PositiveBlockProgram.compile p.1 p.2) := by
  have h : FP blockSeedEncoding formulaEncoding (fun p => p.2.foldl formulaStep (p.1,[])) :=
    ⟨ListFoldMachines.computerOn blockSeedEncoding instructionEncoding formulaEncoding formulaStep
      (fun p => (p.1,[])) Prod.snd (fun _ => rfl) (Classical.choice fp_formulaStep)
      (Polynomial.C 10000*(Polynomial.X+1)^2) block_prefix_size⟩
  exact h.congr (fun p => by simp [fold_formulaStep,PositiveBlockProgram.compile])

end PlanarHom.PositiveBlockProgram
