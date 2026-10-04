import PlanarHom.MixedParallelRuns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PlanarHom.MixedParallelMachines
open PlanarHom.Complexity

private theorem start_frame (selected : ℕ) (d : Data) (w tail : Bits) :
    Runs selected (cfg .startEdge false {d with input:=BitEncoding.frame w++tail})
      (cfg .saveCounter false {d with input:=BitEncoding.frame w++tail}) 1 := by
  cases w with
  | nil => simpa [BitEncoding.frame] using edge_start selected false d false tail
  | cons b bs => simpa [BitEncoding.frame] using edge_start selected false d true (b::(BitEncoding.frame bs++tail))

/-- Save the binary counter, classify the exact edge word, then restore the
counter and all reusable edge data. The only change in control is the match bit. -/
theorem prepare_word (selected : ℕ) (d : Data) (w tail : Bits) (k : ℕ) :
    Runs selected (cfg .startEdge false {d with input:=BitEncoding.frame w++tail,edge:=[],buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k})
      (cfg .route (labelMatches selected w) {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k})
      (2*k+5*w.length+12) := by
  let d₀ : Data := {d with edge:=[],buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k}
  have h₁ := start_frame selected d₀ w tail
  have h₂ := transfer selected false .count .saved (by decide) .saveCounter .edge rfl rfl
    {d₀ with input:=BitEncoding.frame w++tail}
  simp only [d₀,Data.get,Data.set,List.append_nil] at h₂
  have h₃ := edge_run selected false
    {d with edge:=[],buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=[],count:=[]} w tail
  simp only [List.append_nil] at h₃
  have h₄ := transfer selected false .buffer .edge (by decide) .reverseEdge .prepareClass rfl rfl
    {d with input:=tail,edge:=[],buffer:=(BitEncoding.frame w).reverse,saved:=(BitEncoding.nat.encode k).reverse,classifier:=w.reverse,count:=[]}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₄
  have h₅ := transfer selected false .classifier .count (by decide) .prepareClass .tagClass rfl rfl
    {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=w.reverse,count:=[]}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₅
  have h₆ := tag_class selected false
    {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=[],count:=w}
  have h₇ := classify_query selected false
    {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=[]} w
  have h₈ := read_class selected false
    {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=[]} (labelMatches selected w)
  have h₉ := transfer selected (labelMatches selected w) .saved .count (by decide) .restoreCounter .route rfl rfl
    {d with input:=tail,edge:=BitEncoding.frame w,buffer:=[],saved:=(BitEncoding.nat.encode k).reverse,classifier:=[],count:=[]}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₉
  have h := (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans h₉
  apply h.mono
  have hk := encodeNat_length_le k
  simp only [BitEncoding.frame_length]
  omega

/-- Emit exactly one occurrence and increment the preserved canonical counter.
The control flag chooses whether to repeat or to finish this original edge. -/
theorem emit_body (selected : ℕ) (flag : Bool) (d : Data) (k : ℕ) :
    Runs selected (cfg .emit flag {d with buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg (if flag then .check else .clearEdge) flag
        {d with buffer:=[],payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode (k+1)})
      (2*d.edge.length+2*k+6) := by
  have h₁ := transfer₂ selected flag .edge .buffer .payload (by decide) (by decide) (by decide)
    .emit .restoreEdge rfl rfl {d with buffer:=[],count:=BitEncoding.nat.encode k}
  simp only [Data.get,Data.set,List.append_nil] at h₁
  have h₂ := transfer selected flag .buffer .edge (by decide) .restoreEdge .tagInc rfl rfl
    {d with edge:=[],buffer:=d.edge.reverse,payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode k}
  simp only [Data.get,Data.set,List.append_nil,List.reverse_reverse,List.length_reverse] at h₂
  have h₃ : Runs selected (cfg .tagInc flag {d with buffer:=[],payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode k})
      (cfg (if flag then .queryRepeat else .querySingle) flag
        {d with buffer:=[],payload:=d.edge.reverse++d.payload,count:=false::BitEncoding.nat.encode k}) 1 := by
    cases flag
    · exact tag_inc_false selected _
    · exact tag_inc_true selected _
  have h₄ := increment_query selected flag (if flag then .queryRepeat else .querySingle)
    (if flag then .check else .clearEdge) (by cases flag <;> rfl)
    {d with buffer:=[],payload:=d.edge.reverse++d.payload} k
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  convert h using 1
  omega

theorem emit_one (selected : ℕ) (d : Data) (b : Bool) (fs : Bits) (k : ℕ) :
    Runs selected (cfg .check true {d with factor:=b::fs,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .check true {d with factor:=fs,back:=b::d.back,buffer:=[],payload:=d.edge.reverse++d.payload,count:=BitEncoding.nat.encode (k+1)})
      (2*d.edge.length+2*k+7) := by
  have h₁ := check_cons selected true {d with buffer:=[],count:=BitEncoding.nat.encode k} b fs
  have h₂ := emit_body selected true {d with factor:=fs,back:=b::d.back} k
  dsimp only at h₂
  have h := h₁.trans h₂
  convert h using 1
  omega

theorem repeat_run (selected : ℕ) (d : Data) (F w : Bits) (k M : ℕ) (hM : k+F.length≤M) :
    Runs selected (cfg .check true {d with factor:=F,edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .restoreFactor true {d with factor:=[],back:=F.reverse++d.back,edge:=BitEncoding.frame w,buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)})
      (F.length*(2*(BitEncoding.frame w).length+2*M+7)+1) := by
  induction F generalizing d k with
  | nil => simpa using check_nil selected true {d with edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k}
  | cons b fs ih =>
    have h₁ := emit_one selected {d with edge:=BitEncoding.frame w} b fs k
    have hk : 2*(BitEncoding.frame w).length+2*k+7≤2*(BitEncoding.frame w).length+2*M+7 := by omega
    have h₂ := ih {d with back:=b::d.back,payload:=(BitEncoding.frame w).reverse++d.payload}
      (k+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hM)
    have h := (h₁.mono hk).trans h₂
    simpa only [List.length_cons,List.reverse_cons,repeatFrame_succ,List.reverse_append,List.append_assoc,
      List.singleton_append,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h


theorem finish_selected (selected : ℕ) (d : Data) (F w : Bits) (k M : ℕ) (hM : k+F.length≤M) :
    Runs selected (cfg .route true {d with factor:=F,back:=[],edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .startEdge false {d with factor:=F,back:=[],edge:=[],buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)})
      (F.length*(2*(BitEncoding.frame w).length+2*M+7)+F.length+(BitEncoding.frame w).length+5) := by
  have h₁ := route_true selected {d with factor:=F,back:=[],edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k}
  have h₂ := repeat_run selected {d with back:=[]} F w k M hM
  simp only [List.append_nil] at h₂
  have h₃ := transfer selected true .back .factor (by decide) .restoreFactor .clearEdge rfl rfl
    {d with factor:=[],back:=F.reverse,edge:=BitEncoding.frame w,buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₃
  have h₄ := clear selected true .edge .clearEdge .nextEdge rfl rfl
    {d with factor:=F,back:=[],edge:=BitEncoding.frame w,buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)}
  simp only [Data.get,Data.set] at h₄
  have h₅ := next_edge selected true {d with factor:=F,back:=[],edge:=[],buffer:=[],payload:=(repeatFrame F.length w).reverse++d.payload,count:=BitEncoding.nat.encode (k+F.length)}
  have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  convert h using 1
  omega

theorem finish_other (selected : ℕ) (d : Data) (w : Bits) (k : ℕ) :
    Runs selected (cfg .route false {d with edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k})
      (cfg .startEdge false {d with edge:=[],buffer:=[],payload:=(BitEncoding.frame w).reverse++d.payload,count:=BitEncoding.nat.encode (k+1)})
      (3*(BitEncoding.frame w).length+2*k+9) := by
  have h₁ := route_false selected {d with edge:=BitEncoding.frame w,buffer:=[],count:=BitEncoding.nat.encode k}
  have h₂ := emit_body selected false {d with edge:=BitEncoding.frame w} k
  dsimp only at h₂
  have h₃ := clear selected false .edge .clearEdge .nextEdge rfl rfl
    {d with edge:=BitEncoding.frame w,buffer:=[],payload:=(BitEncoding.frame w).reverse++d.payload,count:=BitEncoding.nat.encode (k+1)}
  simp only [Data.get,Data.set] at h₃
  have h₄ := next_edge selected false {d with edge:=[],buffer:=[],payload:=(BitEncoding.frame w).reverse++d.payload,count:=BitEncoding.nat.encode (k+1)}
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  convert h using 1
  omega

def copies (selected s : ℕ) (w : Bits) : ℕ := if labelMatches selected w then s else 1

theorem copies_le (selected s : ℕ) (w : Bits) : copies selected s w≤s+1 := by
  unfold copies
  split <;> omega

/-- Selected occurrences are replicated; every other complete codeword is
copied exactly once. All classifier and counter-save scratch is cleared. -/
theorem one_word (selected : ℕ) (d : Data) (F w tail : Bits) (k M : ℕ) (hM : k+(F.length+1)≤M) :
    Runs selected (cfg .startEdge false {d with input:=BitEncoding.frame w++tail,factor:=F,back:=[],edge:=[],buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k})
      (cfg .startEdge false {d with input:=tail,factor:=F,back:=[],edge:=[],buffer:=[],saved:=[],classifier:=[],payload:=(repeatFrame (copies selected F.length w) w).reverse++d.payload,count:=BitEncoding.nat.encode (k+copies selected F.length w)})
      (40*(F.length+1)*(w.length+M+1)) := by
  have hp := prepare_word selected {d with factor:=F,back:=[]} w tail k
  cases hb : labelMatches selected w with
  | false =>
    rw [hb] at hp
    have hq := finish_other selected {d with input:=tail,factor:=F,back:=[],saved:=[],classifier:=[]} w k
    have h := hp.trans hq
    have hh : copies selected F.length w=1 := by simp [copies,hb]
    rw [hh]
    simp only [repeatFrame_succ,repeatFrame_zero,List.append_nil]
    apply h.mono
    simp only [BitEncoding.frame_length]
    nlinarith
  | true =>
    rw [hb] at hp
    have hq := finish_selected selected {d with input:=tail,saved:=[],classifier:=[]} F w k M (by omega)
    have h := hp.trans hq
    have hh : copies selected F.length w=F.length := by simp [copies,hb]
    rw [hh]
    apply h.mono
    simp only [BitEncoding.frame_length]
    nlinarith

@[simp] theorem selected_cons (selected s : ℕ) (w : Bits) (ws : List Bits) :
    repeatSelected (labelMatches selected) s (w::ws) =
      List.replicate (copies selected s w) w++repeatSelected (labelMatches selected) s ws := by
  cases h : labelMatches selected w <;> simp [repeatSelected_cons,copies,h]

@[simp] theorem frames_selected_cons (selected s : ℕ) (w : Bits) (ws : List Bits) :
    BitEncoding.frames (repeatSelected (labelMatches selected) s (w::ws)) =
      repeatFrame (copies selected s w) w++BitEncoding.frames (repeatSelected (labelMatches selected) s ws) := by
  rw [selected_cons,frames_append]
  rfl

@[simp] theorem selected_length_cons (selected s : ℕ) (w : Bits) (ws : List Bits) :
    (repeatSelected (labelMatches selected) s (w::ws)).length =
      copies selected s w+(repeatSelected (labelMatches selected) s ws).length := by
  rw [selected_cons,List.length_append,List.length_replicate]

theorem frames_selected_length_le (selected s : ℕ) (ws : List Bits) :
    (BitEncoding.frames (repeatSelected (labelMatches selected) s ws)).length≤
      (s+1)*(BitEncoding.frames ws).length := by
  induction ws with
  | nil => simp [BitEncoding.frames]
  | cons w ws ih =>
    rw [frames_selected_cons,List.length_append,repeatFrame_length]
    have hw := Nat.mul_le_mul_right (BitEncoding.frame w).length (copies_le selected s w)
    simpa only [BitEncoding.frames,List.length_append,Nat.mul_add] using Nat.add_le_add hw ih

def wordBudget (F : Bits) (L M : ℕ) : ℕ := 40*(F.length+1)*(L+M+1)

/-- Whole occurrence-list loop, with exact selected-label payload and count,
leaving the encoded unary payload untouched on its separate stack. -/
theorem words_run (selected : ℕ) (d : Data) (F : Bits) (ws : List Bits) (k L M : ℕ)
    (hL : ∀ w∈ws,w.length≤L) (hM : k+(F.length+1)*ws.length≤M) :
    Runs selected (cfg .startEdge false {d with input:=BitEncoding.frames ws,factor:=F,back:=[],edge:=[],buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k})
      (cfg .reversePayload false {d with input:=[],factor:=F,back:=[],edge:=[],buffer:=[],saved:=[],classifier:=[],payload:=(BitEncoding.frames (repeatSelected (labelMatches selected) F.length ws)).reverse++d.payload,count:=BitEncoding.nat.encode (k+(repeatSelected (labelMatches selected) F.length ws).length)})
      (ws.length*wordBudget F L M+1) := by
  induction ws generalizing d k with
  | nil =>
    simpa [BitEncoding.frames] using edge_eof selected false {d with factor:=F,back:=[],edge:=[],buffer:=[],saved:=[],classifier:=[],count:=BitEncoding.nat.encode k}
  | cons w ws ih =>
    have hkm : k+(F.length+1)≤M := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at hM
      omega
    have h₁ := one_word selected d F w (BitEncoding.frames ws) k M hkm
    have hb : 40*(F.length+1)*(w.length+M+1)≤wordBudget F L M :=
      Nat.mul_le_mul_left _ (by have hw:=hL w (by simp); omega)
    have h₂ := ih {d with payload:=(repeatFrame (copies selected F.length w) w).reverse++d.payload}
      (k+copies selected F.length w) (fun z hz=>hL z (by simp [hz])) (by
        have hc:=copies_le selected F.length w
        simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at hM
        omega)
    have h := (h₁.mono hb).trans h₂
    simpa only [BitEncoding.frames,List.length_cons,frames_selected_cons,selected_length_cons,List.reverse_append,
      List.append_assoc,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end PlanarHom.MixedParallelMachines
