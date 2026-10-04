import PlanarHom.MixedParallelFinalize
import PlanarHom.OracleReductionComposition

/-! Genuine polynomial-time selected-label thickening of the exact mixed code. -/

namespace PlanarHom.MixedParallelMachines
open Turing Polynomial PlanarHom.Complexity PlanarHom.MachineComposition

private theorem word_length_le_frames {w : Bits} {ws : List Bits} (hw : w∈ws) :
    w.length≤(BitEncoding.frames ws).length := by
  induction ws with
  | nil => simp at hw
  | cons a as ih =>
    simp only [List.mem_cons] at hw
    simp only [BitEncoding.frames,List.length_append,BitEncoding.frame_length]
    rcases hw with rfl | hw
    · omega
    · have h:=ih hw; omega

private theorem count_le_frames (ws : List Bits) : ws.length≤(BitEncoding.frames ws).length := by
  rw [BitEncoding.frames_length]
  omega

def serialInput (F V H : Bits) (ws : List Bits) (U : Bits) : Bits :=
  BitEncoding.frame F++BitEncoding.frame V++BitEncoding.frame (BitEncoding.frame H++BitEncoding.frames ws)++U

def serialOutput (selected s : ℕ) (V : Bits) (ws : List Bits) (U : Bits) : Bits :=
  BitEncoding.frame V++BitEncoding.frame
    (BitEncoding.frame (BitEncoding.nat.encode (repeatSelected (labelMatches selected) s ws).length)++
      BitEncoding.frames (repeatSelected (labelMatches selected) s ws))++U

noncomputable def oracleTime : Polynomial ℕ := C 128*(X+1)^4

/-- Full raw mixed-framing correctness, including counter classification traffic
and all copies of the unchanged unary payload. -/
theorem raw_run (selected : ℕ) (F V H : Bits) (ws : List Bits) (U : Bits) :
    Runs selected (machine.initial (serialInput F V H ws U))
      (machine.final (serialOutput selected F.length V ws U))
      (128*((serialInput F V H ws U).length+1)^4) := by
  let L := (BitEncoding.frames ws).length
  let M := (F.length+1)*ws.length
  let N := (serialInput F V H ws U).length
  let K := (repeatSelected (labelMatches selected) F.length ws).length
  have h₁ := prefix_run selected F V H (BitEncoding.frames ws) U
  have h₂ := words_run selected {vertices:=(BitEncoding.frame V).reverse,unaries:=U.reverse}
    F.reverse ws 0 L M (fun w hw=>word_length_le_frames hw) (by simp [M])
  simp only [List.length_reverse,Nat.zero_add,List.append_nil] at h₂
  have hzero : BitEncoding.nat.encode 0=[] := by simp [BitEncoding.nat,Computability.encodeNat,Computability.encodeNum]
  rw [hzero] at h₂
  have h₃ := finalize_run selected F.reverse V (BitEncoding.frames (repeatSelected (labelMatches selected) F.length ws)) U K
  have h := (h₁.trans h₂).trans h₃
  apply h.mono
  have hN : N=2*F.length+2*V.length+4*H.length+2*L+U.length+5 := by
    simp only [N,serialInput,List.length_append,BitEncoding.frame_length,L]
    omega
  have hf : F.length≤N := by omega
  have hv : V.length≤N := by omega
  have hu : U.length≤N := by omega
  have hl : L≤N := by omega
  have hm : ws.length≤N := (count_le_frames ws).trans hl
  have hK : K≤M := repeatSelected_length_le (labelMatches selected) F.length ws
  have hM : M≤(N+1)^2 := by
    have hmul:=Nat.mul_le_mul (Nat.add_le_add_right hf 1) (hm.trans (Nat.le_succ N))
    simpa only [Nat.succ_eq_add_one,pow_two] using hmul
  have hp : (BitEncoding.frames (repeatSelected (labelMatches selected) F.length ws)).length≤(N+1)^2 := by
    apply (frames_selected_length_le selected F.length ws).trans
    have hmul:=Nat.mul_le_mul (Nat.add_le_add_right hf 1) (hl.trans (Nat.le_succ N))
    simpa only [Nat.succ_eq_add_one,pow_two] using hmul
  have hsum : L+M+1≤2*(N+1)^2 := by nlinarith
  have hword : ws.length*wordBudget F.reverse L M≤80*(N+1)^4 := by
    have ht:=Nat.mul_le_mul (hm.trans (Nat.le_succ N))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hf 1)) hsum)
    simp only [wordBudget,List.length_reverse]
    convert ht using 1
    simp only [Nat.succ_eq_add_one]
    ring
  have hprefix : F.length+V.length+2*(BitEncoding.frame H++BitEncoding.frames ws).length+
      U.length+H.length+6≤2*N+3 := by
    simp only [List.length_append,BitEncoding.frame_length]
    change _+_+2*(2*H.length+1+L)+_+_+_≤_
    omega
  change (F.length+V.length+2*(BitEncoding.frame H++BitEncoding.frames ws).length+U.length+H.length+6)+
    (ws.length*wordBudget F.reverse L M+1)+
    (4*(BitEncoding.frames (repeatSelected (labelMatches selected) F.length ws)).length+9*K+U.length+
      2*V.length+F.reverse.length+15)≤_
  rw [List.length_reverse]
  have hrest : 13*(N+1)^2+6*N+19≤48*(N+1)^4 := by
    nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3),Nat.zero_le (N^4)]
  nlinarith

/-- Literal codeword equality transports selected-label filtering across the
edge encoding, whose third coordinate is its binary label index. -/
theorem map_selected_edges (selected s : ℕ) (es : List (ℕ × (ℕ × ℕ))) :
    (repeatSelected (fun e=>decide (e.2.2=selected)) s es).map
      (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode =
    repeatSelected (labelMatches selected) s
      (es.map (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.2.2=selected <;>
      simp [repeatSelected_cons,List.map_append,ih,labelMatches_edge,he]

def inputEncoding : BitEncoding (ℕ × MixedCode) := BitEncoding.unaryNat.prod MixedCode.encoding

/-- Exact serialized mixed-code output, with every unselected binary occurrence
and every unary occurrence unchanged. Only the binary count header is recomputed. -/
theorem mixed_run (selected s : ℕ) (g : MixedCode) :
    Runs selected (machine.initial (inputEncoding.encode (s,g)))
      (machine.final (MixedCode.encoding.encode (g.parallelLabel selected s)))
      (oracleTime.eval (inputEncoding.encode (s,g)).length) := by
  let words := g.edges.map (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode
  have h := raw_run selected (BitEncoding.unaryNat.encode s) (BitEncoding.unaryNat.encode g.vertices)
    (BitEncoding.nat.encode g.edges.length) words (MixedCode.unaryEncoding.encode g.unaries)
  have hi : serialInput (BitEncoding.unaryNat.encode s) (BitEncoding.unaryNat.encode g.vertices)
      (BitEncoding.nat.encode g.edges.length) words (MixedCode.unaryEncoding.encode g.unaries) =
      inputEncoding.encode (s,g) := by
    simp [serialInput,inputEncoding,MixedCode.encoding,BitEncoding.retract,BitEncoding.prod,
      BitEncoding.list,MixedCode.unaryEncoding,words,List.append_assoc]
  have ho : serialOutput selected (BitEncoding.unaryNat.encode s).length (BitEncoding.unaryNat.encode g.vertices)
      words (MixedCode.unaryEncoding.encode g.unaries) = MixedCode.encoding.encode (g.parallelLabel selected s) := by
    rw [MixedCode.parallelLabel_encoding]
    simp only [serialOutput,BitEncoding.unaryNat_length,words]
    rw [←map_selected_edges,List.length_map]
    rfl
  rw [hi,ho] at h
  simpa [oracleTime] using h

/-- A genuine ordinary TM2 computer for fixed-selected-label mixed thickening.
The classifier/successor oracle is replaced by its actual proved machine. -/
noncomputable def parallelComputer (selected : ℕ) :
    TM2ComputableInPolyTime inputEncoding.toFinEncoding MixedCode.encoding.toFinEncoding
      (fun p=>p.2.parallelLabel selected p.1) := by
  let c := SelectedLabelOracleMachine.computer selected
  let g := c.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine oracleTime c.time
    outputsFun := ?_ }
  intro p
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost⟩ := mixed_run selected p.1 p.2
  have hN : ∀ k, ((machine.initial (inputEncoding.encode p)).stk k).length≤(inputEncoding.encode p).length :=
    OracleReductionComposition.initial_length machine _
  obtain ⟨n,hn,he⟩ := OracleSubstitution.compiled_run machine g c.time (fun q=>c.outputsFun q) hr _ hN
  refine ⟨{steps:=n,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact hn.trans (OracleReductionComposition.bound_polynomial machine oracleTime c.time
      (inputEncoding.encode p).length cost hcost)

theorem fp_parallelLabel (selected : ℕ) :
    FP inputEncoding MixedCode.encoding (fun p=>p.2.parallelLabel selected p.1) := ⟨parallelComputer selected⟩

end PlanarHom.MixedParallelMachines
