import PlanarHom.ColoringEmitterValidity

/-! NEW exact lookup equations for the numeric canvas/source-reference join. -/
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram

theorem initial_dictionary_get (n i : ℕ) (hi:i<n) :
    (initial n).dictionary[i]?.getD 0=3*i := by
  simp [initial,List.getElem?_map,hi]

theorem step_dictionary_old (s : State) (op : Instruction) (i : ℕ)
    (hi:i<s.dictionary.length) :
    (step s op).dictionary[i]?.getD 0=s.dictionary[i]?.getD 0 := by
  simp only [step,List.getElem?_append_left hi]

theorem step_dictionary_new (s : State) (op : Instruction) (i : ℕ)
    (hlen:s.dictionary.length=s.sourceBase) (hi:i<op.1.template.fresh) :
    (step s op).dictionary[s.sourceBase+i]?.getD 0=
      if i<Macro.outputCount op.1 then s.vertices+3*i else 0 := by
  simp only [step]
  rw [←hlen]
  simp [List.getElem?_append_right,freshDictionary,hi]

theorem fold_dictionary_prefix (ops : List Instruction) (s : State) :
    s.dictionary <+: (ops.foldl step s).dictionary := by
  induction ops generalizing s with
  | nil => exact ⟨[],by simp⟩
  | cons op ops ih =>
    have hstep : s.dictionary <+: (step s op).dictionary := ⟨freshDictionary s.vertices op.1,rfl⟩
    exact hstep.trans (ih (step s op))

theorem fold_edges_prefix (ops : List Instruction) (s : State) :
    s.edges <+: (ops.foldl step s).edges := by
  induction ops generalizing s with
  | nil => exact ⟨[],by simp⟩
  | cons op ops ih =>
    have hstep : s.edges <+: (step s op).edges := ⟨emitEdges s op,rfl⟩
    exact hstep.trans (ih (step s op))

end PlanarHom.ColoringEmitter
