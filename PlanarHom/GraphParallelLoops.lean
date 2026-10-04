import PlanarHom.GraphParallelRuns
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PlanarHom.GraphParallelMachines
open PlanarHom.Complexity

/-- Emit one framed occurrence, restore its reusable copy, and increment the
canonical binary header using the real successor oracle. -/
theorem emit_one (d : Data) (b : Bool) (fs : Bits) (k : ℕ) :
    Runs (cfg .check {d with factor:=b::fs,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .check {d with factor:=fs,back:=b::d.back,buffer:=[], payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode (k+1)})
      (2*d.edge.length+2*k+5) := by
  let d₁ : Data := {d with factor:=fs,back:=b::d.back,buffer:=[],count:=BitEncoding.nat.encode k}
  have h₁ := check_cons {d with buffer:=[],count:=BitEncoding.nat.encode k} b fs
  have h₂ := transfer₂ .edge .buffer .payload (by decide) (by decide) (by decide)
    .emit .restoreEdge rfl rfl d₁
  simp only [d₁,Data.get,Data.set,List.append_nil] at h₂
  have h₃ := transfer .buffer .edge (by decide) .restoreEdge .query rfl rfl
    {d with factor:=fs,back:=b::d.back,edge:=[],buffer:=d.edge.reverse, payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode k}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₃
  have h₄ := query_count {d with factor:=fs,back:=b::d.back,buffer:=[], payload:=d.edge.reverse++d.payload} k
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  convert h using 1
  omega

/-- Consume exactly the unary repetition markers. The original edge remains
available after every copy, and the caller's other stacks stay unchanged. -/
theorem repeat_run (d : Data) (F w : Bits) (k M : ℕ) (hM : k+F.length ≤ M) :
    Runs (cfg .check {d with factor:=F,edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .restoreFactor {d with factor:=[],back:=F.reverse++d.back, edge:=BitEncoding.frame w,buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload, count:=BitEncoding.nat.encode (k+F.length)})
      (F.length*(2*(BitEncoding.frame w).length+2*M+5)+1) := by
  induction F generalizing d k with
  | nil =>
    simpa using check_nil {d with edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k}
  | cons b fs ih =>
    have h₁ := emit_one {d with edge:=BitEncoding.frame w} b fs k
    have hk : 2*(BitEncoding.frame w).length+2*k+5 ≤ 2*(BitEncoding.frame w).length+2*M+5 := by omega
    have h₁' := h₁.mono hk
    have h₂ := ih {d with back:=b::d.back,payload:=(BitEncoding.frame w).reverse++d.payload}
      (k+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hM)
    have h := h₁'.trans h₂
    simpa only [List.length_cons,List.reverse_cons,repeatFrame_succ,List.reverse_append,
      List.append_assoc,List.singleton_append,Nat.add_mul,Nat.one_mul,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using h


/-- One whole original edge occurrence is replicated and the unary counter is
restored for the next occurrence. Endpoint codewords are never interpreted. -/
theorem one_word (d : Data) (F w tail : Bits) (k M : ℕ) (hM : k+F.length ≤ M) :
    Runs (cfg .edge {d with input:=BitEncoding.frame w++tail,factor:=F,back:=[],edge:=[],buffer:=[], count:=BitEncoding.nat.encode k})
      (cfg .edge {d with input:=tail,factor:=F,back:=[],edge:=[],buffer:=[], payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)})
      (10*(F.length+1)*(w.length+M+1)) := by
  have h₁ := edge_run {d with factor:=F,back:=[],edge:=[],buffer:=[],count:=BitEncoding.nat.encode k} w tail
  simp only [List.append_nil] at h₁
  have h₂ := transfer .buffer .edge (by decide) .reverseEdge .check rfl rfl
    {d with input:=tail,factor:=F,back:=[],edge:=[],buffer:=(BitEncoding.frame w).reverse, count:=BitEncoding.nat.encode k}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₂
  have h₃ := repeat_run {d with input:=tail,back:=[]} F w k M hM
  simp only [List.append_nil] at h₃
  have h₄ := transfer .back .factor (by decide) .restoreFactor .clearEdge rfl rfl
    {d with input:=tail,factor:=[],back:=F.reverse,edge:=BitEncoding.frame w,buffer:=[], payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₄
  have h₅ := clear .edge .clearEdge .edge rfl rfl
    {d with input:=tail,factor:=F,back:=[],edge:=BitEncoding.frame w,buffer:=[], payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)}
  simp only [Data.get,Data.set] at h₅
  have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  apply h.mono
  simp only [BitEncoding.frame_length]
  nlinarith


def wordBudget (F : Bits) (L M : ℕ) : ℕ := 10*(F.length+1)*(L+M+1)

/-- Iterate over the actual framed occurrence list, preserving exact order and
multiplicity and counting every emitted occurrence in canonical binary. -/
theorem words_run (d : Data) (F : Bits) (ws : List Bits) (k L M : ℕ)
    (hL : ∀ w ∈ ws, w.length ≤ L) (hM : k+F.length*ws.length ≤ M) :
    Runs (cfg .edge {d with input:=BitEncoding.frames ws,factor:=F,back:=[],edge:=[],buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .reversePayload {d with input:=[],factor:=F,back:=[],edge:=[],buffer:=[],payload:=(BitEncoding.frames (repeatWords F.length ws)).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length*ws.length)})
      (ws.length*wordBudget F L M+1) := by
  induction ws generalizing d k with
  | nil => simpa [BitEncoding.frames] using edge_eof {d with factor:=F,back:=[],edge:=[],buffer:=[],count:=BitEncoding.nat.encode k}
  | cons w ws ih =>
    have hkm : k+F.length ≤ M := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at hM
      omega
    have h₁ := one_word d F w (BitEncoding.frames ws) k M hkm
    have hb : 10*(F.length+1)*(w.length+M+1) ≤ wordBudget F L M :=
      Nat.mul_le_mul_left _ (by have hw := hL w (by simp); omega)
    have h₁' := h₁.mono hb
    have h₂ := ih {d with payload:=(repeatFrame F.length w).reverse++d.payload}
      (k+F.length) (fun z hz => hL z (by simp [hz]))
      (by simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hM)
    have h := h₁'.trans h₂
    simpa only [BitEncoding.frames,List.length_cons,frames_repeatWords_cons,List.reverse_append,
      List.append_assoc,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using h

end PlanarHom.GraphParallelMachines
