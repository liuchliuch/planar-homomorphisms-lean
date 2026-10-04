import PlanarHom.ColoringEmitterStepMachines

/-! NEW explicit polynomial growth of every reachable accumulator, including
arbitrary malformed source references. Dictionary fallback is the literal zero. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace Macro
 theorem addresses_fields (k : Kind) : ∀a∈addresses k,a.2.1≤1300 ∧ a.2.2≤2 := by
  cases k <;> decide +kernel
 theorem edges_length_le (k : Kind) : (edges k).length≤3152 := by cases k <;> decide +kernel
 theorem outputCount_le (k : Kind) : outputCount k≤2 := by cases k <;> decide
 theorem addedVertices_le (k : Kind) : addedVertices k≤1264 := by cases k <;> decide
 theorem fresh_le (k : Kind) : k.template.fresh≤15 := by cases k <;> decide
 theorem address_fields (k : Kind) (v : ℕ) : (address k v).2.1≤1300 ∧ (address k v).2.2≤2 := by
  by_cases hv:v<(addresses k).length
  · simp only [address,List.getElem?_eq_getElem hv,Option.getD_some]
    exact addresses_fields k _ (List.getElem_mem hv)
  · simp [address,List.getElem?_eq_none (by omega : (addresses k).length≤v)]
end Macro

structure State.Bounded (s : State) (B : ℕ) : Prop where
  source_le : s.sourceBase≤B
  vertices_le : s.vertices≤B
  dictionary_le : ∀x∈s.dictionary,x≤B
  edges_le : ∀e∈s.edges,e.1≤B ∧ e.2.1≤B ∧ e.2.2=0

theorem localVertex_le (op : Instruction) (ds : List ℕ) (base v B : ℕ)
    (hd : ∀x∈ds,x≤B) (hb : base≤B) : localVertex op ds base v≤B+5000 := by
  have ha:=Macro.address_fields op.1 v
  have hc:=Macro.outputCount_le op.1
  have hi:=getRef_le ds (inputRef op (Macro.address op.1 v).2.1) B hd
  change ds[inputRef op (Macro.address op.1 v).2.1]?.getD 0≤B at hi
  dsimp only [localVertex]
  split_ifs <;> omega

theorem step_bounded (s : State) (op : Instruction) (B : ℕ) (hs : s.Bounded B) :
    (step s op).Bounded (B+5000) := by
  have hcount:=Macro.addedVertices_le op.1
  have hfresh:=Macro.fresh_le op.1
  have hsource:=hs.source_le
  have hvertices:=hs.vertices_le
  refine ⟨by dsimp [step]; omega,by dsimp [step]; omega,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact (hs.dictionary_le x hx).trans (by omega)
    · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
      have hc:=Macro.outputCount_le op.1
      split_ifs <;> omega
  · intro e he
    rcases List.mem_append.mp he with he|he
    · have hh:=hs.edges_le e he
      exact ⟨hh.1.trans (by omega),hh.2.1.trans (by omega),hh.2.2⟩
    · obtain ⟨e,he,rfl⟩:=List.mem_map.mp he
      exact ⟨localVertex_le op s.dictionary s.vertices e.1 B hs.dictionary_le hs.vertices_le,
        localVertex_le op s.dictionary s.vertices e.2 B hs.dictionary_le hs.vertices_le,rfl⟩

theorem initial_bounded (n : ℕ) : (initial n).Bounded (3*n) := by
  refine ⟨by dsimp [initial]; omega,by rfl,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
    have hh:=List.mem_range.mp hi
    omega
  · simp [initial]

theorem fold_bounded (ops : List Instruction) (s : State) (B : ℕ) (hs : s.Bounded B) :
    (ops.foldl step s).Bounded (B+5000*ops.length) := by
  induction ops generalizing s B with
  | nil => simpa using hs
  | cons op ops ih =>
    have hh:=ih (step s op) (B+5000) (step_bounded s op B hs)
    simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem step_dictionary_length (s : State) (op : Instruction) :
    (step s op).dictionary.length≤s.dictionary.length+15 := by
  have hh:=Macro.fresh_le op.1
  simp only [step,List.length_append,freshDictionary,List.length_map,List.length_range]
  omega

theorem step_edges_length (s : State) (op : Instruction) :
    (step s op).edges.length≤s.edges.length+3152 := by
  have hh:=Macro.edges_length_le op.1
  simp only [step,List.length_append,emitEdges,List.length_map]
  omega

theorem fold_lengths (ops : List Instruction) (s : State) :
    (ops.foldl step s).dictionary.length≤s.dictionary.length+15*ops.length ∧
    (ops.foldl step s).edges.length≤s.edges.length+3152*ops.length := by
  induction ops generalizing s with
  | nil => simp
  | cons op ops ih =>
    have hh:=ih (step s op)
    have hd:=step_dictionary_length s op
    have he:=step_edges_length s op
    simp only [List.foldl_cons,List.length_cons]
    constructor <;> omega

theorem list_code_bound {A : Type} (ea : BitEncoding A) (xs : List A) (B : ℕ)
    (h : ∀x∈xs,(ea.encode x).length≤B) : (ea.list.encode xs).length≤(2*B+3)*xs.length+1 := by
  have hn:=Complexity.encodeNat_length_le xs.length
  have hs:=List.sum_le_card_nsmul (xs.map (fun x=>(ea.encode x).length)) B (by
    intro v hv
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hv
    exact h x hx)
  simp only [List.length_map,smul_eq_mul] at hs
  have he : (ea.list.encode xs).length=2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun x=>(ea.encode x).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  rw [he]
  change (BitEncoding.nat.encode xs.length).length≤xs.length at hn
  nlinarith

theorem state_code_bound (s : State) (B : ℕ) (hs : s.Bounded B) :
    (stateEncoding.encode s).length≤100*(B+1)*(s.dictionary.length+s.edges.length+1) := by
  have hd:=list_code_bound BitEncoding.nat s.dictionary B
    (fun x hx=>(Complexity.encodeNat_length_le x).trans (hs.dictionary_le x hx))
  have he:=list_code_bound edgeEncoding s.edges (5*B+2) (by
    intro e he
    have hb:=hs.edges_le e he
    have h1:=(Complexity.encodeNat_length_le e.1).trans hb.1
    have h2:=(Complexity.encodeNat_length_le e.2.1).trans hb.2.1
    simp only [edgeEncoding,referenceEncoding,BitEncoding.prod_length,hb.2.2]
    have h0 : (BitEncoding.nat.encode 0).length≤0 := Complexity.encodeNat_length_le 0
    omega)
  have hc : (stateEncoding.encode s).length=2*s.sourceBase+2*(BitEncoding.nat.list.encode s.dictionary).length+
      2*s.vertices+(edgeEncoding.list.encode s.edges).length+3 := by
    simp [stateEncoding,statePartsEncoding,BitEncoding.retract,BitEncoding.prod_length]
    omega
  rw [hc]
  nlinarith [hs.source_le,hs.vertices_le]

end PlanarHom.ColoringEmitter
