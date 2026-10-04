import PlanarHom.ColoringEmitterMacroValidity

/-! NEW exact source-width/dictionary invariants and unconditional validity of
the emitted numeric graph. Malformed references still use the total zero default. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram ParsimoniousNorOneInThree

theorem fold_sourceBase (ops : List Instruction) (s : State) :
    (ops.foldl step s).sourceBase=width s.sourceBase ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simpa only [List.foldl_cons,step,width] using ih (step s op)

theorem run_sourceBase (n : ℕ) (ops : List Instruction) : (run n ops).sourceBase=width n ops :=
  fold_sourceBase ops (initial n)

theorem fold_dictionary_length (ops : List Instruction) (s : State)
    (hs:s.dictionary.length=s.sourceBase) :
    (ops.foldl step s).dictionary.length=(ops.foldl step s).sourceBase := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih =>
    apply ih
    simp [step,freshDictionary,hs]

theorem run_dictionary_length (n : ℕ) (ops : List Instruction) :
    (run n ops).dictionary.length=width n ops := by
  rw [←run_sourceBase]
  exact fold_dictionary_length ops (initial n) (by simp [initial])

structure State.Valid (s : State) : Prop where
  dictionary_valid : ∀x∈s.dictionary,x+2<s.vertices
  edges_valid : ∀e∈s.edges,e.1<s.vertices ∧ e.2.1<s.vertices ∧ e.2.2=0

theorem localVertex_lt (op : Instruction) (ds : List ℕ) (base v : ℕ)
    (hd : ∀x∈ds,x+2<base) (hv : v<Macro.vertexCount op.1) :
    localVertex op ds base v<base+Macro.addedVertices op.1 := by
  have hi:=getRef_le ds (inputRef op (Macro.address op.1 v).2.1) base
    (fun x hx=>(Nat.le_of_lt (hd x hx)).trans' (by omega))
  change ds[inputRef op (Macro.address op.1 v).2.1]?.getD 0≤base at hi
  have ha:=Macro.address_valid op.1 v hv
  have hadd:=Macro.addedVertices_eq op.1
  have hpos:=Macro.addedVertices_ge op.1
  dsimp only [localVertex]
  rcases ha with ⟨ht,hj,hc⟩|⟨ht,hj,hc⟩|⟨ht,hj,hc⟩
  · simp [ht]
    omega
  · simp [ht]
    omega
  · simp only [ht,show ¬(2:ℕ)=0 by omega,show ¬(2:ℕ)=1 by omega,if_false]
    omega

theorem initial_valid (n : ℕ) : (initial n).Valid := by
  constructor
  · intro x hx
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
    have hh:=List.mem_range.mp hi
    dsimp [initial]
    omega
  · simp [initial]

theorem step_valid (s : State) (op : Instruction) (hs:s.Valid) : (step s op).Valid := by
  have hadd:=Macro.addedVertices_eq op.1
  have hpos:=Macro.addedVertices_ge op.1
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh:=hs.dictionary_valid x hx
      dsimp [step]
      omega
    · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
      dsimp [step]
      split_ifs <;> omega
  · intro e he
    rcases List.mem_append.mp he with he|he
    · have hh:=hs.edges_valid e he
      dsimp [step]
      exact ⟨by omega,by omega,hh.2.2⟩
    · dsimp only [emitEdges] at he
      obtain ⟨localEdge,hlocal,himage⟩:=List.mem_map.mp he
      rw [←himage]
      have hv:=Macro.edges_valid op.1 localEdge hlocal
      exact ⟨localVertex_lt op s.dictionary s.vertices localEdge.1 hs.dictionary_valid hv.1,
        localVertex_lt op s.dictionary s.vertices localEdge.2 hs.dictionary_valid hv.2,rfl⟩

theorem fold_valid (ops : List Instruction) (s : State) (hs:s.Valid) : (ops.foldl step s).Valid := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih => exact ih _ (step_valid s op hs)

theorem run_valid (n : ℕ) (ops : List Instruction) : (run n ops).Valid :=
  fold_valid ops (initial n) (initial_valid n)

theorem graphOf_valid (s : State) (hs:s.Valid) : (graphOf s).Valid 1 0 := by
  constructor
  · intro e he
    have hh:=hs.edges_valid e he
    exact ⟨hh.1,hh.2.1,by rw [hh.2.2]; omega⟩
  · simp [graphOf]

/-- Every typed raw formula produces a well-indexed one-label graph; its separate
semantic correspondence is promised only on valid source formulas. -/
theorem compile_valid (f : NumericFormula) : (compile f).Valid 1 0 := by
  unfold compile
  split_ifs
  · simp [MixedCode.Valid]
  · exact graphOf_valid _ (run_valid _ _)

end PlanarHom.ColoringEmitter
