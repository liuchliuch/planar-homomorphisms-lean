import PlanarHom.NondeterministicTM2
import PlanarHom.NondeterministicRunCombinators
import PlanarHom.MachinePairing
import PlanarHom.InputLengthMachine
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.FiniteReachableAlphabetMachines

/-! Genuine binary branching between a deterministic preparation machine and verifier.
Preparation emits `frame x ++ unary n`. The generator consumes one unary symbol
per binary choice, physically builds the witness, and restores the framed input. -/
namespace PlanarHom.CertificateGeneratorMachine
noncomputable section
open Turing Turing.TM2 Complexity MachineComposition NondeterministicComputationTree
open OracleSubstitution hiding Phase Label phase program machine cfg_ext

inductive Phase | scan | generate | choose | push (b : Bool) | restore
  deriving DecidableEq, Fintype
abbrev Labels (a b : FinTM2) := Phase ⊕ (a.Λ ⊕ b.Λ)
def leftLabel {a b : FinTM2} (l : a.Λ) : Labels a b := .inr (.inl l)
def rightLabel {a b : FinTM2} (l : b.Λ) : Labels a b := .inr (.inr l)
def phase {a b : FinTM2} (p : Phase) : Labels a b := .inl p

def leftStmt (a b : FinTM2) (q : a.Stmt) : Stmt (Alphabet a b) (Labels a b) (State a b) :=
  redirectHalt (phase .scan)
    (renameState (callerState a b) (liftStmt (callerEmbedding a b) leftLabel q))
def rightStmt (a b : FinTM2) (q : b.Stmt) : Stmt (Alphabet a b) (Labels a b) (State a b) :=
  renameState (calleeState a b) (liftStmt (calleeEmbedding a b) rightLabel q)

def program (a b : TM2ComputableAux Bool Bool) : Labels a.tm b.tm →
    Stmt (Alphabet a.tm b.tm) (Labels a.tm b.tm) (State a.tm b.tm)
  | .inl .scan => .pop (.inl a.tm.k₁) (fun v z => (v.1,z.map a.outputAlphabet))
      (.branch (fun v => v.2.getD false)
        (.pop (.inl a.tm.k₁) (fun v z => (v.1,z.map a.outputAlphabet))
          (.push temp (fun _ => true) (.push temp (fun v => v.2.getD false)
            (.load (fun v => (v.1,none)) (.goto (fun _ => phase .scan))))))
        (.push temp (fun _ => false) (.load (fun v => (v.1,none))
          (.goto (fun _ => phase .generate)))))
  | .inl .generate => .pop (.inl a.tm.k₁) (fun v z => (v.1,z.map a.outputAlphabet))
      (.branch (fun v => v.2.isSome)
        (.load (fun v => (v.1,none)) (.goto (fun _ => phase .choose)))
        (.goto (fun _ => phase .restore)))
  | .inl .choose => .halt
  | .inl (.push z) => .push (.inr (.inl b.tm.k₀)) (fun _ => b.inputAlphabet.symm z)
      (.goto (fun _ => phase .generate))
  | .inl .restore => transferStmt temp (.inr (.inl b.tm.k₀)) id b.inputAlphabet.symm
      (phase .restore) (rightLabel b.tm.main)
  | .inr (.inl l) => leftStmt a.tm b.tm (a.tm.m l)
  | .inr (.inr l) => rightStmt a.tm b.tm (b.tm.m l)

def deterministicCore (a b : TM2ComputableAux Bool Bool) : FinTM2 := by
  letI := a.tm.kFin; letI := b.tm.kFin; letI := a.tm.ΛFin; letI := b.tm.ΛFin
  letI := a.tm.σFin; letI := b.tm.σFin
  exact {
    K := Bank a.tm b.tm
    Γ := Alphabet a.tm b.tm
    k₀ := .inl a.tm.k₀
    k₁ := .inr (.inl b.tm.k₁)
    Λ := Labels a.tm b.tm
    main := leftLabel a.tm.main
    σ := State a.tm b.tm
    initialState := ((a.tm.initialState,b.tm.initialState),none)
    Γk₀Fin := a.tm.Γk₀Fin
    m := program a b }

def core (a b : TM2ComputableAux Bool Bool) : TM2ComputableAux Bool Bool where
  tm := deterministicCore a b
  inputAlphabet := a.inputAlphabet
  outputAlphabet := b.outputAlphabet

def machine (a b : TM2ComputableAux Bool Bool)
    (ha : ∀ k, Fintype (a.tm.Γ k)) (hb : ∀ k, Fintype (b.tm.Γ k)) :
    NondeterministicTM2.Machine where
  core := core a b
  finiteAlphabet
    | .inl k => ha k
    | .inr (.inl k) => hb k
    | .inr (.inr _) => inferInstanceAs (Fintype Bool)
  branch
    | .inl .choose => some (phase (.push false),phase (.push true))
    | _ => none

def leftCfg (a b : FinTM2) (c : a.Cfg) :
    Cfg (Alphabet a b) (Labels a b) (State a b) :=
  ⟨(c.l.map leftLabel).or (some (phase .scan)),((c.var,b.initialState),none),
    store a b c.stk (fun _ => []) []⟩
def rightCfg (a b : FinTM2) (c : b.Cfg) :
    Cfg (Alphabet a b) (Labels a b) (State a b) :=
  ⟨c.l.map rightLabel,((a.initialState,c.var),none),store a b (fun _ => []) c.stk []⟩

theorem leftStmt_correct (a b : FinTM2) (q : a.Stmt) (v : a.σ)
    (A : ∀ k,List (a.Γ k)) :
    stepAux (leftStmt a b q) ((v,b.initialState),none) (store a b A (fun _ => []) []) =
      leftCfg a b (stepAux q v A) := by
  unfold leftStmt
  rw [redirectHalt_correct]
  let e := callerEmbedding a b
  have hs : e.Represents A (store a b A (fun _ => []) []) := by
    intro k; change A k = (A k).map id; simp
  have hh := liftStmt_correct e (leftLabel (a:=a) (b:=b)) q v
    (b.initialState,(none : Option Bool)) A (store a b A (fun _ => []) []) hs
  change continueCfg _ (stepAux (renameState (callerState a b) (liftStmt e leftLabel q))
    ((callerState a b) (v,(b.initialState,none))) _) = _
  rw [renameState_correct]
  apply OracleSubstitution.cfg_ext
  · exact congrArg (fun l => l.or (some (phase .scan))) hh.1
  · exact congrArg (callerState a b) hh.2.1
  · funext k
    cases k with
    | inl k =>
      have hh' := hh.2.2 k
      change _ = List.map id _ at hh'
      simpa only [List.map_id] using hh' 
    | inr k =>
      have ht := liftStmt_untouched e (leftLabel (a:=a) (b:=b)) q (v,(b.initialState,(none : Option Bool)))
        (store a b A (fun _ => []) []) (.inr k) (by intro j; simp [e,callerEmbedding])
      cases k <;> exact ht

theorem rightStmt_correct (a b : FinTM2) (q : b.Stmt) (v : b.σ)
    (B : ∀ k,List (b.Γ k)) :
    stepAux (rightStmt a b q) ((a.initialState,v),none) (store a b (fun _ => []) B []) =
      rightCfg a b (stepAux q v B) := by
  let e := calleeEmbedding a b
  have hs : e.Represents B (store a b (fun _ => []) B []) := by
    intro k; change B k = (B k).map id; simp
  have h := liftStmt_correct e (rightLabel (a:=a) (b:=b)) q v
    (a.initialState,(none : Option Bool)) B (store a b (fun _ => []) B []) hs
  change stepAux (renameState (calleeState a b) (liftStmt e rightLabel q))
    ((calleeState a b) (v,(a.initialState,none))) _ = _
  rw [renameState_correct]
  apply OracleSubstitution.cfg_ext
  · exact h.1
  · exact congrArg (calleeState a b) h.2.1
  · funext k
    cases k with
    | inl k =>
      exact liftStmt_untouched e rightLabel q (v,(a.initialState,none)) _ (.inl k)
        (by intro j; simp [e,calleeEmbedding])
    | inr k => cases k with
      | inl k =>
        have hh := h.2.2 k
        change _ = List.map id _ at hh
        simpa only [List.map_id] using hh
      | inr u =>
        exact liftStmt_untouched e rightLabel q (v,(a.initialState,none)) _ (.inr (.inr u))
          (by intro j; simp [e,calleeEmbedding])

variable (a b : TM2ComputableAux Bool Bool)
variable (ha : ∀ k, Fintype (a.tm.Γ k)) (hb : ∀ k, Fintype (b.tm.Γ k))

abbrev M := machine a b ha hb

def stage (p : Phase) (xs ys T : Bits) : (core a b).tm.Cfg :=
  ⟨some (phase p),((a.tm.initialState,b.tm.initialState),none),
    store a.tm b.tm (pointStack a.tm.k₁ (xs.map a.outputAlphabet.symm))
      (pointStack b.tm.k₀ (ys.map b.inputAlphabet.symm)) T⟩

theorem initial_eq (x : Bits) : (M a b ha hb).initial x =
    leftCfg a.tm b.tm (initList a.tm (x.map a.inputAlphabet.symm)) := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp only [NondeterministicTM2.Machine.initial,initList_stk,leftCfg,core,machine]
    change pointStack (.inl a.tm.k₀) _ = store a.tm b.tm (pointStack a.tm.k₀ _) (fun _=>[]) []
    simp only [pointStack,←store_update_left,store_empty]
    rfl

theorem left_view (c d : a.tm.Cfg) (h : a.tm.step c = some d) :
    (M a b ha hb).view (leftCfg a.tm b.tm c) = .ordinary (leftCfg a.tm b.tm d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at h
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at h
    subst d
    change NodeView.ordinary (stepAux (leftStmt a.tm b.tm (a.tm.m l)) _ _) = _
    exact congrArg NodeView.ordinary (leftStmt_correct a.tm b.tm (a.tm.m l) v S)

theorem right_view (c d : b.tm.Cfg) (h : b.tm.step c = some d) :
    (M a b ha hb).view (rightCfg a.tm b.tm c) = .ordinary (rightCfg a.tm b.tm d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at h
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at h
    subst d
    change NodeView.ordinary (stepAux (rightStmt a.tm b.tm (b.tm.m l)) _ _) = _
    exact congrArg NodeView.ordinary (rightStmt_correct a.tm b.tm (b.tm.m l) v S)

theorem left_handoff (x : Bits) :
    leftCfg a.tm b.tm (haltList a.tm (x.map a.outputAlphabet.symm)) = stage a b .scan x [] [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp [leftCfg,stage,haltList_stk,pointStack,Function.update_eq_self]

theorem right_handoff (x : Bits) :
    stage a b .restore [] x [] =
      ⟨some (phase .restore),((a.tm.initialState,b.tm.initialState),none),
        store a.tm b.tm (fun _ => []) (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm)) []⟩ := by
  simp [stage,pointStack,Function.update_eq_self]

theorem scan_nil (rest T : Bits) :
    (M a b ha hb).view (stage a b .scan (false :: rest) [] T) =
      .ordinary (stage a b .generate rest [] (false :: T)) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,pointStack,
    stepAux,store_update_left,store_update_temp]

theorem scan_cons (z : Bool) (rest T : Bits) :
    (M a b ha hb).view (stage a b .scan (true :: z :: rest) [] T) =
      .ordinary (stage a b .scan rest [] (z :: true :: T)) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,pointStack,
    stepAux,store_update_left,store_update_temp]

theorem generate_nil (w T : Bits) :
    (M a b ha hb).view (stage a b .generate [] w T) =
      .ordinary (stage a b .restore [] w T) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,pointStack,
    stepAux,store_update_left,Function.update_eq_self]

theorem generate_cons (z : Bool) (zs w T : Bits) :
    (M a b ha hb).view (stage a b .generate (z::zs) w T) =
      .ordinary (stage a b .choose zs w T) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,pointStack,
    stepAux,store_update_left]

theorem choose_view (zs w T : Bits) :
    (M a b ha hb).view (stage a b .choose zs w T) =
      .binary (stage a b (.push false) zs w T) (stage a b (.push true) zs w T) := rfl

theorem push_view (z : Bool) (zs w T : Bits) :
    (M a b ha hb).view (stage a b (.push z) zs w T) =
      .ordinary (stage a b .generate zs (z::w) T) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,pointStack,
    stepAux,store_update_right]

theorem restore_nil (w : Bits) :
    (M a b ha hb).view (stage a b .restore [] w []) =
      .ordinary (rightCfg a.tm b.tm (initList b.tm (w.map b.inputAlphabet.symm))) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,
    rightCfg,initList_stk,pointStack,transferStmt,stepAux,store_update_temp,Function.update_eq_self]
  rfl

theorem restore_cons (z : Bool) (w T : Bits) :
    (M a b ha hb).view (stage a b .restore [] w (z::T)) =
      .ordinary (stage a b .restore [] (z::w) T) := by
  simp [NondeterministicTM2.Machine.view,machine,core,deterministicCore,program,phase,stage,
    pointStack,transferStmt,stepAux,store_update_temp,store_update_right]

/-- Restoring the input prefix has exactly one path and a linear transition count. -/
theorem restore_bounded (T w : Bits) (fuel : ℕ)
    (h : Bounded (M a b ha hb).view
      (rightCfg a.tm b.tm (initList b.tm ((T.reverse++w).map b.inputAlphabet.symm))) fuel) :
    Bounded (M a b ha hb).view (stage a b .restore [] w T) (T.length+1+fuel) := by
  induction T generalizing w with
  | nil => simpa only [List.length_nil,Nat.zero_add,Nat.add_comm] using
      Bounded.ordinary (restore_nil a b ha hb w) h
  | cons z T ih =>
    have ht := ih (z::w) (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using h)
    simpa only [List.length_cons,Nat.add_right_comm] using
      Bounded.ordinary (restore_cons a b ha hb z w T) ht

theorem restore_count (T w : Bits) (fuel : ℕ) :
    acceptingCount (M a b ha hb).view (T.length+1+fuel) (stage a b .restore [] w T) =
      acceptingCount (M a b ha hb).view fuel
        (rightCfg a.tm b.tm (initList b.tm ((T.reverse++w).map b.inputAlphabet.symm))) := by
  induction T generalizing w with
  | nil => simp [Nat.add_comm 1 fuel,acceptingCount,restore_nil]
  | cons z T ih =>
    rw [List.length_cons,Nat.add_right_comm T.length 1 1,Nat.add_right_comm (T.length+1) 1 fuel]
    simp only [acceptingCount,restore_cons]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (z::w)

/-- Framed-input scanning is deterministic and consumes one transition per data
bit and one transition for the terminator. -/
theorem scan_bounded (x rest T : Bits) (fuel : ℕ)
    (h : Bounded (M a b ha hb).view
      (stage a b .generate rest [] ((BitEncoding.frame x).reverse++T)) fuel) :
    Bounded (M a b ha hb).view (stage a b .scan (BitEncoding.frame x++rest) [] T)
      (x.length+1+fuel) := by
  induction x generalizing T with
  | nil => simpa [BitEncoding.frame,Nat.add_comm] using
      Bounded.ordinary (scan_nil a b ha hb rest T) h
  | cons z x ih =>
    have ht := ih (z::true::T) (by
      simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc] using h)
    simpa only [BitEncoding.frame,List.cons_append,List.length_cons,Nat.add_right_comm] using
      Bounded.ordinary (scan_cons a b ha hb z (BitEncoding.frame x++rest) T) ht

theorem scan_count (x rest T : Bits) (fuel : ℕ) :
    acceptingCount (M a b ha hb).view (x.length+1+fuel)
      (stage a b .scan (BitEncoding.frame x++rest) [] T) =
    acceptingCount (M a b ha hb).view fuel
      (stage a b .generate rest [] ((BitEncoding.frame x).reverse++T)) := by
  induction x generalizing T with
  | nil => simp [BitEncoding.frame,Nat.add_comm 1 fuel,acceptingCount,scan_nil]
  | cons z x ih =>
    rw [List.length_cons,Nat.add_right_comm x.length 1 1,Nat.add_right_comm (x.length+1) 1 fuel]
    simp only [BitEncoding.frame,List.cons_append,acceptingCount,scan_cons]
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc] using ih (z::true::T)

theorem right_halt_view (z : Bool) :
    (M a b ha hb).view (rightCfg a.tm b.tm (haltList b.tm ([z].map b.outputAlphabet.symm))) =
      if z then .accept else .reject := by
  cases z <;>
    simp [NondeterministicTM2.Machine.view,NondeterministicTM2.Machine.output,machine,core,
      deterministicCore,rightCfg,haltList] <;>
    exact b.outputAlphabet.apply_symm_apply _

theorem verifier_correct (x : Bits) (z : Bool) (fuel : ℕ)
    (h : TM2OutputsInTime b.tm (x.map b.inputAlphabet.symm)
      (some ([z].map b.outputAlphabet.symm)) fuel) :
    Bounded (M a b ha hb).view (rightCfg a.tm b.tm (initList b.tm (x.map b.inputAlphabet.symm))) fuel ∧
    acceptingCount (M a b ha hb).view fuel
      (rightCfg a.tm b.tm (initList b.tm (x.map b.inputAlphabet.symm))) = if z then 1 else 0 := by
  have hf (k : ℕ) : Bounded (M a b ha hb).view
      (rightCfg a.tm b.tm (haltList b.tm ([z].map b.outputAlphabet.symm))) k := by
    cases z
    · exact .reject (right_halt_view a b ha hb false)
    · exact .accept (right_halt_view a b ha hb true)
  have hc (k : ℕ) : acceptingCount (M a b ha hb).view k
      (rightCfg a.tm b.tm (haltList b.tm ([z].map b.outputAlphabet.symm))) = if z then 1 else 0 := by
    cases z
    · exact acceptingCount_reject _ (right_halt_view a b ha hb false) _
    · exact acceptingCount_accept _ (right_halt_view a b ha hb true) _
  have ht := NondeterministicRunCombinators.bounded_of_iterate b.tm.step (M a b ha hb).view
    (rightCfg a.tm b.tm) (fun {c d} => right_view a b ha hb c d) h.evals_in_steps (hf (fuel-h.steps))
  have he := NondeterministicRunCombinators.acceptingCount_of_iterate b.tm.step (M a b ha hb).view
    (rightCfg a.tm b.tm) (fun {c d} => right_view a b ha hb c d)
    (fuel:=fuel-h.steps) h.evals_in_steps
  rw [Nat.add_sub_of_le h.steps_le_m] at ht he
  exact ⟨ht,he.trans (hc _)⟩

end
end PlanarHom.CertificateGeneratorMachine
