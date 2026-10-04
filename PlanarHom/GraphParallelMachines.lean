import PlanarHom.GraphParallelFinalize

/-! Actual polynomial-time replication of serialized graph edge occurrences. -/

namespace PlanarHom.GraphParallelMachines
open Turing Turing.TM2 Polynomial PlanarHom.Complexity PlanarHom.MachineComposition

private theorem word_length_le_frames {w : Bits} {ws : List Bits} (hw : w ∈ ws) :
    w.length ≤ (BitEncoding.frames ws).length := by
  induction ws with
  | nil => simp at hw
  | cons a as ih =>
    simp only [List.mem_cons] at hw
    simp only [BitEncoding.frames,List.length_append,BitEncoding.frame_length]
    rcases hw with rfl | hw
    · omega
    · have h := ih hw; omega

private theorem count_le_frames (ws : List Bits) : ws.length ≤ (BitEncoding.frames ws).length := by
  rw [BitEncoding.frames_length]
  omega

def serialInput (F V H : Bits) (ws : List Bits) : Bits :=
  BitEncoding.frame F++BitEncoding.frame V++BitEncoding.frame H++BitEncoding.frames ws

def serialOutput (s : ℕ) (V : Bits) (ws : List Bits) : Bits :=
  BitEncoding.frame V++BitEncoding.frame (BitEncoding.nat.encode (s*ws.length))++
    BitEncoding.frames (repeatWords s ws)

/-- A conservative charged-time polynomial for the whole concrete oracle
program. The quartic bound includes all counter queries and complete answers. -/
noncomputable def oracleTime : Polynomial ℕ := C 30*(X+1)^4

/-- Whole-program serialized correctness and charged polynomial cost, before
eliminating the actual polynomial-time successor subroutine. -/
theorem raw_run (F V H : Bits) (ws : List Bits) :
    Runs (machine.initial (serialInput F V H ws))
      (machine.final (serialOutput F.length V ws))
      (30*((serialInput F V H ws).length+1)^4) := by
  let L := (BitEncoding.frames ws).length
  let M := F.length*ws.length
  let N := (serialInput F V H ws).length
  have h₁ := prefix_run F V H (BitEncoding.frames ws)
  have h₂ := words_run {vertices:=(BitEncoding.frame V).reverse} F.reverse ws 0 L M
    (fun w hw=>word_length_le_frames hw) (by simp [M])
  simp only [List.length_reverse,Nat.zero_add,List.append_nil] at h₂
  have hzero : BitEncoding.nat.encode 0 = [] := by
    simp [BitEncoding.nat,Computability.encodeNat,Computability.encodeNum]
  rw [hzero] at h₂
  have h₃ := finalize_run F.reverse V (BitEncoding.frames (repeatWords F.length ws)) M
  have h := (h₁.trans h₂).trans h₃
  apply h.mono
  have hN : N = 2*F.length+2*V.length+2*H.length+L+3 := by
    simp only [N,serialInput,List.length_append,BitEncoding.frame_length,L]
    omega
  have hf : F.length ≤ N := by omega
  have hv : V.length ≤ N := by omega
  have hl : L ≤ N := by omega
  have hm : ws.length ≤ N := (count_le_frames ws).trans hl
  have hM : M ≤ N*N := Nat.mul_le_mul hf hm
  have hp : (BitEncoding.frames (repeatWords F.length ws)).length ≤ N*N := by
    rw [frames_repeatWords_length]
    exact Nat.mul_le_mul hf hl
  have hsum : L+M+1 ≤ (N+1)^2 := by nlinarith
  have hword : ws.length*wordBudget F.reverse L M ≤ 10*(N+1)^4 := by
    have ht := Nat.mul_le_mul (hm.trans (Nat.le_succ N))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 10 (Nat.add_le_add_right hf 1)) hsum)
    simpa only [wordBudget,List.length_reverse] using
      (show ws.length*(10*(F.length+1)*(L+M+1)) ≤ 10*(N+1)^4 from by
        convert ht using 1
        simp only [Nat.succ_eq_add_one]
        ring)
  have hprefix : F.length+V.length+H.length+3 ≤ N := by omega
  change (F.length+V.length+H.length+3)+(ws.length*wordBudget F.reverse L M+1)+
    ((BitEncoding.frames (repeatWords F.length ws)).length+3*M+2*V.length+F.reverse.length+8) ≤ _
  rw [List.length_reverse]
  nlinarith [Nat.zero_le N, Nat.zero_le (N^2),Nat.zero_le (N^3),Nat.zero_le (N^4)]

/-- The selected input format exposes the numeric multiplier in unary, so the
number of emitted occurrences is honestly bounded by the input bit length. -/
def inputEncoding : BitEncoding (ℕ × GraphCode) := BitEncoding.unaryNat.prod GraphCode.encoding

/-- The complete occurrence transformation is proved against the exact
serialized graph code, including the recomputed binary length header. -/
theorem graph_run (s : ℕ) (g : GraphCode) :
    Runs (machine.initial (inputEncoding.encode (s,g)))
      (machine.final (GraphCode.encoding.encode (g.parallel s)))
      (oracleTime.eval (inputEncoding.encode (s,g)).length) := by
  have h := raw_run (BitEncoding.unaryNat.encode s) (BitEncoding.unaryNat.encode g.vertices)
    (BitEncoding.nat.encode g.edges.length) (g.edges.map (BitEncoding.nat.prod BitEncoding.nat).encode)
  have hi : serialInput (BitEncoding.unaryNat.encode s) (BitEncoding.unaryNat.encode g.vertices)
      (BitEncoding.nat.encode g.edges.length) (g.edges.map (BitEncoding.nat.prod BitEncoding.nat).encode) =
      inputEncoding.encode (s,g) := by
    simp [serialInput,inputEncoding,GraphCode.encoding,BitEncoding.retract,BitEncoding.prod,
      BitEncoding.list,List.append_assoc]
  have ho : serialOutput (BitEncoding.unaryNat.encode s).length (BitEncoding.unaryNat.encode g.vertices)
      (g.edges.map (BitEncoding.nat.prod BitEncoding.nat).encode) = GraphCode.encoding.encode (g.parallel s) := by
    rw [GraphCode.parallel_encoding]
    simp [serialOutput,BitEncoding.unaryNat_length]
  rw [hi,ho] at h
  simpa [oracleTime] using h

/-- Actual ordinary finite-control TM2 computation of graph occurrence
replication. The successor oracle is eliminated by the proved subroutine
compiler; no arithmetic or graph-processing primitive is assumed. -/
noncomputable def parallelComputer :
    TM2ComputableInPolyTime inputEncoding.toFinEncoding GraphCode.encoding.toFinEncoding
      (fun p => p.2.parallel p.1) := by
  let g := successorBitsComputer.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine oracleTime successorBitsComputer.time
    outputsFun := ?_ }
  intro p
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost⟩ := graph_run p.1 p.2
  have hN : ∀ k, ((machine.initial (inputEncoding.encode p)).stk k).length ≤
      (inputEncoding.encode p).length := OracleReductionComposition.initial_length machine _
  obtain ⟨n,hn,he⟩ := OracleSubstitution.compiled_run machine g successorBitsComputer.time
    (fun q=>successorBitsComputer.outputsFun q) hr _ hN
  refine ⟨{steps:=n,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact hn.trans (OracleReductionComposition.bound_polynomial machine oracleTime
      successorBitsComputer.time (inputEncoding.encode p).length cost hcost)

theorem fp_parallel : FP inputEncoding GraphCode.encoding (fun p=>p.2.parallel p.1) := ⟨parallelComputer⟩


/-- The explicit unary multiplier also gives a direct quadratic bound on the
actual serialized output, independently of the compiler's looser time bound. -/
theorem parallel_output_length (s : ℕ) (g : GraphCode) :
    (GraphCode.encoding.encode (g.parallel s)).length ≤
      4*((inputEncoding.encode (s,g)).length+1)^2 := by
  let N := (inputEncoding.encode (s,g)).length
  let L := (BitEncoding.frames (g.edges.map (BitEncoding.nat.prod BitEncoding.nat).encode)).length
  have hN : N = 2*s+1+(GraphCode.encoding.encode g).length := by
    simp [N,inputEncoding,BitEncoding.prod_length,BitEncoding.unaryNat_length,Nat.add_assoc,Nat.add_comm]
  have hg : (GraphCode.encoding.encode g).length = 2*g.vertices+1+
      (2*(BitEncoding.nat.encode g.edges.length).length+1)+L := by
    simp [GraphCode.encoding,BitEncoding.retract,BitEncoding.prod,BitEncoding.list,
      BitEncoding.unaryNat_length,BitEncoding.frame_length,L]
    omega
  have hs : s ≤ N := by omega
  have hv : g.vertices ≤ N := by omega
  have hm : g.edges.length ≤ N := by have h := g.size_le_length; omega
  have hL : L ≤ N := by omega
  have hsm : s*g.edges.length ≤ N*N := Nat.mul_le_mul hs hm
  have hsl : s*L ≤ N*N := Nat.mul_le_mul hs hL
  have hc := encodeNat_length_le (s*g.edges.length)
  have hout : (GraphCode.encoding.encode (g.parallel s)).length =
      2*g.vertices+1+(2*(BitEncoding.nat.encode (s*g.edges.length)).length+1)+s*L := by
    rw [GraphCode.parallel_encoding]
    simp only [List.length_append,BitEncoding.frame_length,BitEncoding.unaryNat_length,
      frames_repeatWords_length,L]
  rw [hout]
  change _ ≤ 4*(N+1)^2
  nlinarith

end PlanarHom.GraphParallelMachines
