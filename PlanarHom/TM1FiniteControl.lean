import PlanarHom.TM1PrimitiveTimeBounds
import PlanarHom.SingleTapeNondeterministic
import PlanarHom.NondeterministicBlockSimulation

/-! # Finite primitive control with explicit procedure boundaries

A primitive compiler for a finitely supported TM1 program. Procedure entries
retain their labels, so a caller can intercept a designated entry with a binary
choice. Halt is a separate boundary available to an output-checking routine.
-/
namespace PlanarHom.TM1FiniteControl
open Turing

variable {Γ Λ σ : Type} [Inhabited Γ]

/-- `inl l` is a procedure entry, `inr (some q)` a residual statement,
and `inr none` the halt boundary. -/
abbrev RawState (Γ Λ σ : Type) := (Λ ⊕ Option (TM1.Stmt Γ Λ σ)) × σ
abbrev RawCfg (Γ Λ σ : Type) [Inhabited Γ] := RawState Γ Λ σ × Tape Γ

def applyStmt (s : TM0.Stmt Γ) (t : Tape Γ) : Tape Γ :=
  match s with | .move d => t.move d | .write a => t.write a

def aux (a : Γ) : TM1.Stmt Γ Λ σ → σ → RawState Γ Λ σ × TM0.Stmt Γ
  | .move d q,v => ((.inr (some q),v),.move d)
  | .write f q,v => ((.inr (some q),v),.write (f a v))
  | .load f q,v => aux a q (f a v)
  | .branch f q r,v => if f a v then aux a q v else aux a r v
  | .goto f,v => ((.inl (f a v),v),.write a)
  | .halt,v => ((.inr none,v),.write a)

def rawTransition (M : Λ → TM1.Stmt Γ Λ σ) :
    RawState Γ Λ σ → Γ → Option (RawState Γ Λ σ × TM0.Stmt Γ)
  | (.inl l,v),a => some (aux a (M l) v)
  | (.inr (some q),v),a => some (aux a q v)
  | (.inr none,_),_ => none

def rawStep (M : Λ → TM1.Stmt Γ Λ σ) (c : RawCfg Γ Λ σ) : Option (RawCfg Γ Λ σ) :=
  (rawTransition M c.1 c.2.head).map fun (q,s) => (q,applyStmt s c.2)

def rawIter (M : Λ → TM1.Stmt Γ Λ σ) (n : ℕ) (c : RawCfg Γ Λ σ) : Option (RawCfg Γ Λ σ) :=
  (fun c : Option (RawCfg Γ Λ σ) => c.bind (rawStep M))^[n] (some c)

def boundary (c : TM1.Cfg Γ Λ σ) : RawCfg Γ Λ σ :=
  ((match c.l with | some l => .inl l | none => .inr none,c.var),c.Tape)

def residual (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) : RawCfg Γ Λ σ :=
  ((.inr (some q),v),t)

theorem rawIter_eq_of_step_eq (M : Λ → TM1.Stmt Γ Λ σ)
    {c d : RawCfg Γ Λ σ} (n : ℕ) (hn : 0<n) (h : rawStep M c=rawStep M d) :
    rawIter M n c=rawIter M n d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp only [rawIter,Function.iterate_succ_apply,Option.bind_some,h]

/-- Exact primitive duration, with the final procedure label retained. -/
theorem raw_compile_exact (M : Λ → TM1.Stmt Γ Λ σ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) :
    rawIter M (TM1PrimitiveTimeBounds.steps q v t) (residual q v t) =
      some (boundary (TM1.stepAux q v t)) := by
  induction q generalizing v t with
  | move d q ih =>
    rw [TM1PrimitiveTimeBounds.steps,Nat.add_comm,rawIter,Function.iterate_succ_apply]
    change rawIter M (TM1PrimitiveTimeBounds.steps q v (t.move d)) (residual q v (t.move d)) = _
    exact ih _ _
  | write f q ih =>
    rw [TM1PrimitiveTimeBounds.steps,Nat.add_comm,rawIter,Function.iterate_succ_apply]
    change rawIter M (TM1PrimitiveTimeBounds.steps q v (t.write (f t.head v)))
      (residual q v (t.write (f t.head v))) = _
    exact ih _ _
  | load f q ih =>
    change rawIter M (TM1PrimitiveTimeBounds.steps q (f t.head v) t)
      (residual (.load f q) v t) = _
    rw [rawIter_eq_of_step_eq M _ (TM1PrimitiveTimeBounds.steps_pos q (f t.head v) t)
      (show rawStep M (residual (.load f q) v t) = rawStep M (residual q (f t.head v) t) from rfl)]
    exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f t.head v with
    | false =>
      simp only [TM1PrimitiveTimeBounds.steps,h,Bool.false_eq_true,if_false]
      rw [rawIter_eq_of_step_eq M _ (TM1PrimitiveTimeBounds.steps_pos r v t)
        (show rawStep M (residual (.branch f q r) v t)=rawStep M (residual r v t) by
          simp [rawStep,rawTransition,residual,aux,h])]
      simpa [TM1.stepAux,h] using ihr v t
    | true =>
      simp only [TM1PrimitiveTimeBounds.steps,h,if_true]
      rw [rawIter_eq_of_step_eq M _ (TM1PrimitiveTimeBounds.steps_pos q v t)
        (show rawStep M (residual (.branch f q r) v t)=rawStep M (residual q v t) by
          simp [rawStep,rawTransition,residual,aux,h])]
      simpa [TM1.stepAux,h] using ihq v t
  | goto f => simp [rawIter,TM1PrimitiveTimeBounds.steps,rawStep,rawTransition,residual,aux,
      boundary,TM1.stepAux,applyStmt,Tape.write_self]
  | halt => simp [rawIter,TM1PrimitiveTimeBounds.steps,rawStep,rawTransition,residual,aux,
      boundary,TM1.stepAux,applyStmt,Tape.write_self]

/-- An entry consumes the body's first primitive itself, adding no dispatch cost. -/
theorem raw_entry_exact (M : Λ → TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) (t : Tape Γ) :
    rawIter M (TM1PrimitiveTimeBounds.steps (M l) v t) ((.inl l,v),t) =
      some (boundary (TM1.stepAux (M l) v t)) := by
  rw [rawIter_eq_of_step_eq M _ (TM1PrimitiveTimeBounds.steps_pos (M l) v t)
    (show rawStep M ((.inl l,v),t)=rawStep M (residual (M l) v t) from rfl)]
  exact raw_compile_exact M _ _ _

/-- Stop at every procedure entry. Only residual syntax executes, so a
completed block cannot accidentally cross an externally intercepted boundary. -/
def rawResidualStep (c : RawCfg Γ Λ σ) : Option (RawCfg Γ Λ σ) :=
  match c.1.1 with
  | .inl _ => none
  | .inr _ => rawStep (fun _ => TM1.Stmt.halt) c

def rawResidualIter (n : ℕ) (c : RawCfg Γ Λ σ) : Option (RawCfg Γ Λ σ) :=
  (fun c : Option (RawCfg Γ Λ σ) => c.bind rawResidualStep)^[n] (some c)

theorem rawResidualIter_eq_of_step_eq
    {c d : RawCfg Γ Λ σ} (n : ℕ) (hn : 0<n) (h : rawResidualStep c=rawResidualStep d) :
    rawResidualIter n c=rawResidualIter n d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp only [rawResidualIter,Function.iterate_succ_apply,Option.bind_some,h]

/-- Exact primitive duration, with the final procedure label retained. -/
theorem raw_residual_compile_exact
    (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) :
    rawResidualIter (TM1PrimitiveTimeBounds.steps q v t) (residual q v t) =
      some (boundary (TM1.stepAux q v t)) := by
  induction q generalizing v t with
  | move d q ih =>
    rw [TM1PrimitiveTimeBounds.steps,Nat.add_comm,rawResidualIter,Function.iterate_succ_apply]
    change rawResidualIter (TM1PrimitiveTimeBounds.steps q v (t.move d)) (residual q v (t.move d)) = _
    exact ih _ _
  | write f q ih =>
    rw [TM1PrimitiveTimeBounds.steps,Nat.add_comm,rawResidualIter,Function.iterate_succ_apply]
    change rawResidualIter (TM1PrimitiveTimeBounds.steps q v (t.write (f t.head v)))
      (residual q v (t.write (f t.head v))) = _
    exact ih _ _
  | load f q ih =>
    change rawResidualIter (TM1PrimitiveTimeBounds.steps q (f t.head v) t)
      (residual (.load f q) v t) = _
    rw [rawResidualIter_eq_of_step_eq _ (TM1PrimitiveTimeBounds.steps_pos q (f t.head v) t)
      (show rawResidualStep (residual (.load f q) v t) = rawResidualStep (residual q (f t.head v) t) from rfl)]
    exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f t.head v with
    | false =>
      simp only [TM1PrimitiveTimeBounds.steps,h,Bool.false_eq_true,if_false]
      rw [rawResidualIter_eq_of_step_eq _ (TM1PrimitiveTimeBounds.steps_pos r v t)
        (show rawResidualStep (residual (.branch f q r) v t)=rawResidualStep (residual r v t) by
          simp [rawResidualStep,rawResidualStep,rawStep,rawTransition,residual,aux,h])]
      simpa [TM1.stepAux,h] using ihr v t
    | true =>
      simp only [TM1PrimitiveTimeBounds.steps,h,if_true]
      rw [rawResidualIter_eq_of_step_eq _ (TM1PrimitiveTimeBounds.steps_pos q v t)
        (show rawResidualStep (residual (.branch f q r) v t)=rawResidualStep (residual q v t) by
          simp [rawResidualStep,rawResidualStep,rawStep,rawTransition,residual,aux,h])]
      simpa [TM1.stepAux,h] using ihq v t
  | goto f => simp [rawResidualIter,TM1PrimitiveTimeBounds.steps,rawResidualStep,rawStep,rawTransition,residual,aux,
      boundary,TM1.stepAux,applyStmt,Tape.write_self]
  | halt => simp [rawResidualIter,TM1PrimitiveTimeBounds.steps,rawResidualStep,rawStep,rawTransition,residual,aux,
      boundary,TM1.stepAux,applyStmt,Tape.write_self]

section Restriction
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)

/-- The entire control space is a sum/product of finite sets. -/
abbrev State := (↥S ⊕ ↥(TM1.stmts M S)) × σ
abbrev Cfg := State M S × Tape Γ

def forget (q : State M S) : RawState Γ Λ σ :=
  (q.1.elim (fun l => .inl l.val) (fun r => .inr r.val),q.2)

def forgetCfg (c : Cfg M S) : RawCfg Γ Λ σ := (forget M S c.1,c.2)

def Valid (q : RawState Γ Λ σ) : Prop :=
  q.1.elim (fun l => l∈S) (fun r => r∈TM1.stmts M S)

def pack (q : RawState Γ Λ σ) (h : Valid M S q) : State M S :=
  by
    rcases q with ⟨l,v⟩
    cases l with
    | inl l => exact (.inl ⟨l,h⟩,v)
    | inr r => exact (.inr ⟨r,h⟩,v)

omit [Inhabited Γ] in
@[simp] theorem forget_pack (q : RawState Γ Λ σ) (h : Valid M S q) :
    forget M S (pack M S q h)=q := by rcases q with ⟨l,v⟩; cases l <;> rfl

omit [Inhabited Γ] in
@[simp] theorem valid_forget (q : State M S) : Valid M S (forget M S q) := by
  rcases q with ⟨l,v⟩; cases l with | inl l => exact l.property | inr r => exact r.property

omit [Inhabited Γ] in
theorem forget_injective : Function.Injective (forget M S) := by
  rintro ⟨a,v⟩ ⟨b,w⟩ h
  cases a <;> cases b <;> simp_all [forget,Subtype.ext_iff]

theorem forgetCfg_injective : Function.Injective (forgetCfg M S) := by
  rintro ⟨q,t⟩ ⟨r,u⟩ h
  have hp := Prod.mk.inj h
  exact Prod.ext (forget_injective M S hp.1) hp.2

variable [Inhabited Λ] (ss : TM1.Supports M S)
include ss

omit [Inhabited Γ] in
/-- The compiler uses only residual syntax already in mathlib's finite support. -/
theorem aux_valid (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S) (a : Γ) (v : σ) :
    Valid M S (aux a q v).1 := by
  have hs := TM1.stmts_supportsStmt ss hq
  induction q generalizing v with
  | move d q =>
    exact TM1.stmts_trans (by
      classical
      simp [TM1.stmts₁,TM1.stmts₁_self]) hq
  | write f q =>
    exact TM1.stmts_trans (by
      classical
      simp [TM1.stmts₁,TM1.stmts₁_self]) hq
  | load f q ih =>
    exact ih (TM1.stmts_trans (by
      classical
      simp [TM1.stmts₁,TM1.stmts₁_self]) hq) _ hs
  | branch f q r ihq ihr =>
    cases h : f a v with
    | false =>
      simp only [aux,h,Bool.false_eq_true,if_false]
      exact ihr (TM1.stmts_trans (by
      classical
      simp [TM1.stmts₁,TM1.stmts₁_self]) hq) v hs.2
    | true =>
      simp only [aux,h,if_true]
      exact ihq (TM1.stmts_trans (by
      classical
      simp [TM1.stmts₁,TM1.stmts₁_self]) hq) v hs.1
  | goto f => exact hs a v
  | halt => simp [Valid,aux,TM1.stmts]

omit ss [Inhabited Γ] [Inhabited Λ] in
theorem body_mem (l : Λ) (hl : l∈S) : some (M l)∈TM1.stmts M S := by
  classical
  simp only [TM1.stmts,Finset.some_mem_insertNone,Finset.mem_biUnion]
  exact ⟨l,hl,TM1.stmts₁_self⟩

omit [Inhabited Γ] in
theorem rawTransition_valid (q : RawState Γ Λ σ) (hq : Valid M S q)
    (a : Γ) {r : RawState Γ Λ σ} {s : TM0.Stmt Γ}
    (h : rawTransition M q a=some (r,s)) : Valid M S r := by
  rcases q with ⟨l,v⟩
  cases l with
  | inl l =>
    have hv := aux_valid M S ss (M l) (body_mem M S l hq) a v
    simp only [rawTransition,Option.some.injEq] at h
    simpa [h] using hv
  | inr l =>
    cases l with
    | none => cases h
    | some q =>
      have hv := aux_valid M S ss q hq a v
      simp only [rawTransition,Option.some.injEq] at h
      simpa [h] using hv

noncomputable def transition (q : State M S) (a : Γ) : Option (State M S × TM0.Stmt Γ) :=
  match h : rawTransition M (forget M S q) a with
  | none => none
  | some (r,s) => some (pack M S r (rawTransition_valid M S ss _ (valid_forget M S q) a h),s)

theorem transition_entry (l : Λ) (hl : l∈S) (v : σ) (a : Γ) :
    transition M S ss (.inl ⟨l,hl⟩,v) a =
      some (pack M S (aux a (M l) v).1
        (aux_valid M S ss (M l) (body_mem M S l hl) a v),(aux a (M l) v).2) := by
  simp [transition,forget,rawTransition]

theorem transition_residual (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S)
    (v : σ) (a : Γ) :
    transition M S ss (.inr ⟨some q,hq⟩,v) a =
      some (pack M S (aux a q v).1 (aux_valid M S ss q hq a v),(aux a q v).2) := by
  simp [transition,forget,rawTransition]

theorem transition_halt (v : σ) (a : Γ) (h : none∈TM1.stmts M S) :
    transition M S ss (.inr ⟨none,h⟩,v) a=none := rfl

noncomputable def step (c : Cfg M S) : Option (Cfg M S) :=
  (transition M S ss c.1 c.2.head).map fun (q,s) => (q,applyStmt s c.2)

noncomputable def iter (n : ℕ) (c : Cfg M S) : Option (Cfg M S) :=
  (fun c : Option (Cfg M S) => c.bind (step M S ss))^[n] (some c)

/-- Execute residual syntax only, retaining entry and halt boundaries for the caller. -/
noncomputable def residualStep (c : Cfg M S) : Option (Cfg M S) :=
  match c.1.1 with
  | .inl _ => none
  | .inr _ => step M S ss c

noncomputable def residualIter (n : ℕ) (c : Cfg M S) : Option (Cfg M S) :=
  (fun c : Option (Cfg M S) => c.bind (residualStep M S ss))^[n] (some c)

/-- This is an actual finite type whenever the local store is finite. -/
noncomputable instance [Fintype σ] : Fintype (State M S) := inferInstance

/-- Restriction changes neither the primitive command nor its duration. -/
theorem transition_forget (q : State M S) (a : Γ) :
    (transition M S ss q a).map (fun (r,s) => (forget M S r,s)) =
      rawTransition M (forget M S q) a := by
  unfold transition
  split <;> simp_all

theorem step_forget (c : Cfg M S) :
    (step M S ss c).map (forgetCfg M S) = rawStep M (forgetCfg M S c) := by
  have ht := congrArg (Option.map (fun (q,s) => (q,applyStmt s c.2)))
    (transition_forget M S ss c.1 c.2.head)
  simpa [step,rawStep,forgetCfg,Option.map_map,Function.comp_def] using ht

/-- Restriction preserves every exact iteration, including divergence and halt. -/
theorem iterate_forget (n : ℕ) (c : Option (Cfg M S)) :
    ((fun x : Option (Cfg M S) => x.bind (step M S ss))^[n] c).map (forgetCfg M S) =
      (fun x : Option (RawCfg Γ Λ σ) => x.bind (rawStep M))^[n] (c.map (forgetCfg M S)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    congr 1
    cases c with
    | none => rfl
    | some c => exact step_forget M S ss c

theorem residualStep_forget (c : Cfg M S) :
    (residualStep M S ss c).map (forgetCfg M S)=rawResidualStep (forgetCfg M S c) := by
  rcases c with ⟨⟨q,v⟩,t⟩
  cases q with
  | inl l => rfl
  | inr r =>
    have hs := step_forget M S ss ((.inr r,v),t)
    cases h : r.val <;>
      simpa [residualStep,rawResidualStep,forgetCfg,forget,rawStep,rawTransition,h] using hs

theorem residualIterate_forget (n : ℕ) (c : Option (Cfg M S)) :
    ((fun x : Option (Cfg M S) => x.bind (residualStep M S ss))^[n] c).map (forgetCfg M S) =
      (fun x : Option (RawCfg Γ Λ σ) => x.bind rawResidualStep)^[n] (c.map (forgetCfg M S)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    congr 1
    cases c with
    | none => rfl
    | some c => exact residualStep_forget M S ss c

omit ss in
def startResidual (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S)
    (v : σ) (t : Tape Γ) : Cfg M S := ((.inr ⟨some q,hq⟩,v),t)

omit ss in
def startEntry (l : Λ) (hl : l∈S) (v : σ) (t : Tape Γ) : Cfg M S :=
  ((.inl ⟨l,hl⟩,v),t)

omit ss in
/-- Pack a supported TM1 boundary while preserving its label and entire tape. -/
def startBoundary (c : TM1.Cfg Γ Λ σ) (hc : c.l∈Finset.insertNone S) : Cfg M S := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => exact ((.inr ⟨none,by simp [TM1.stmts]⟩,v),t)
  | some l => exact startEntry M S l (Finset.some_mem_insertNone.mp hc) v t

omit ss [Inhabited Λ] in
@[simp] theorem forgetCfg_startBoundary (c : TM1.Cfg Γ Λ σ) (hc : c.l∈Finset.insertNone S) :
    forgetCfg M S (startBoundary M S c hc)=boundary c := by
  rcases c with ⟨l,v,t⟩
  cases l <;> rfl

omit ss [Inhabited Λ] in
theorem supports_stepAux (q : TM1.Stmt Γ Λ σ) (hq : TM1.SupportsStmt S q)
    (v : σ) (t : Tape Γ) : (TM1.stepAux q v t).l∈Finset.insertNone S := by
  induction q generalizing v t with
  | move d q ih => exact ih hq _ _
  | write f q ih => exact ih hq _ _
  | load f q ih => exact ih hq _ _
  | branch f q r ihq ihr =>
    cases h : f t.head v <;> simp only [TM1.stepAux,h,Bool.cond_false,Bool.cond_true]
    · exact ihr hq.2 _ _
    · exact ihq hq.1 _ _
  | goto f => exact Finset.some_mem_insertNone.mpr (hq _ _)
  | halt => simp [TM1.stepAux]

/-- A finite-control execution realizes the precise statement cost and result. -/
theorem compile_exact (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S)
    (v : σ) (t : Tape Γ) :
    ∃ d : Cfg M S,
      iter M S ss (TM1PrimitiveTimeBounds.steps q v t) (startResidual M S q hq v t)=some d ∧
      forgetCfg M S d=boundary (TM1.stepAux q v t) := by
  have hi := iterate_forget M S ss (TM1PrimitiveTimeBounds.steps q v t)
    (some (startResidual M S q hq v t))
  change (iter M S ss _ _).map (forgetCfg M S)=rawIter M _ (residual q v t) at hi
  rw [raw_compile_exact] at hi
  exact Option.map_eq_some_iff.mp hi

theorem entry_exact (l : Λ) (hl : l∈S) (v : σ) (t : Tape Γ) :
    ∃ d : Cfg M S,
      iter M S ss (TM1PrimitiveTimeBounds.steps (M l) v t) (startEntry M S l hl v t)=some d ∧
      forgetCfg M S d=boundary (TM1.stepAux (M l) v t) := by
  have hi := iterate_forget M S ss (TM1PrimitiveTimeBounds.steps (M l) v t)
    (some (startEntry M S l hl v t))
  change (iter M S ss _ _).map (forgetCfg M S)=rawIter M _ ((.inl l,v),t) at hi
  rw [raw_entry_exact] at hi
  exact Option.map_eq_some_iff.mp hi

/-- Exact execution using only residual states before the final boundary.
This theorem remains usable when entry labels are intercepted by binary choices. -/
theorem residual_compile_exact (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S)
    (v : σ) (t : Tape Γ) :
    ∃ d : Cfg M S,
      residualIter M S ss (TM1PrimitiveTimeBounds.steps q v t)
        (startResidual M S q hq v t)=some d ∧
      forgetCfg M S d=boundary (TM1.stepAux q v t) := by
  have hi := residualIterate_forget M S ss (TM1PrimitiveTimeBounds.steps q v t)
    (some (startResidual M S q hq v t))
  change (residualIter M S ss _ _).map (forgetCfg M S)=rawResidualIter _ (residual q v t) at hi
  rw [raw_residual_compile_exact] at hi
  exact Option.map_eq_some_iff.mp hi

/-- The exact finite endpoint, with proof fields hidden by proof irrelevance. -/
theorem residual_compile_exact_boundary (q : TM1.Stmt Γ Λ σ)
    (hq : some q∈TM1.stmts M S) (v : σ) (t : Tape Γ) :
    residualIter M S ss (TM1PrimitiveTimeBounds.steps q v t) (startResidual M S q hq v t) =
      some (startBoundary M S (TM1.stepAux q v t)
        (supports_stepAux S q (TM1.stmts_supportsStmt ss hq) v t)) := by
  obtain ⟨d,hd,he⟩ := residual_compile_exact M S ss q hq v t
  rw [hd]
  congr 1
  apply forgetCfg_injective M S
  simpa using he

/-- Transfer a statement block to any target view. Only residual transitions
need to be ordinary; the final entry/halt boundary is unconstrained. -/
theorem statement_run {D : Type*} (view : D → NondeterministicComputationTree.NodeView D)
    (embed : Cfg M S → D)
    (ordinary : ∀ {c d}, residualStep M S ss c=some d → view (embed c)=.ordinary (embed d))
    (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S) (v : σ) (t : Tape Γ) :
    NondeterministicBlockSimulation.OrdinaryRun view (TM1PrimitiveTimeBounds.steps q v t)
      (embed (startResidual M S q hq v t))
      (embed (startBoundary M S (TM1.stepAux q v t)
        (supports_stepAux S q (TM1.stmts_supportsStmt ss hq) v t))) :=
  NondeterministicBlockSimulation.OrdinaryRun.of_iterate (residualStep M S ss) embed ordinary
    (residual_compile_exact_boundary M S ss q hq v t)

/-- The initial entry has the same first primitive as its body residual. -/
theorem entry_step (l : Λ) (hl : l∈S) (v : σ) (t : Tape Γ) :
    step M S ss (startEntry M S l hl v t) =
      residualStep M S ss (startResidual M S (M l) (body_mem M S l hl) v t) := by
  apply Option.map_injective (forgetCfg_injective M S)
  rw [step_forget,residualStep_forget]
  rfl

/-- Enter one selected procedure and stop at its next boundary. Only this
entry needs an ordinary equation, so other entries may be binary choices. -/
theorem entry_run {D : Type*} (view : D → NondeterministicComputationTree.NodeView D)
    (embed : Cfg M S → D)
    (ordinary : ∀ {c d}, residualStep M S ss c=some d → view (embed c)=.ordinary (embed d))
    (l : Λ) (hl : l∈S) (v : σ) (t : Tape Γ)
    (entry_ordinary : ∀ {d}, step M S ss (startEntry M S l hl v t)=some d →
      view (embed (startEntry M S l hl v t))=.ordinary (embed d)) :
    NondeterministicBlockSimulation.OrdinaryRun view (TM1PrimitiveTimeBounds.steps (M l) v t)
      (embed (startEntry M S l hl v t))
      (embed (startBoundary M S (TM1.stepAux (M l) v t)
        (supports_stepAux S (M l) (ss.2 l hl) v t))) := by
  have hr := residual_compile_exact_boundary M S ss (M l) (body_mem M S l hl) v t
  cases ht : TM1PrimitiveTimeBounds.steps (M l) v t with
  | zero => have hp := TM1PrimitiveTimeBounds.steps_pos (M l) v t; omega
  | succ n =>
    rw [ht] at hr
    obtain ⟨next,hs,hr⟩ := NondeterministicRunCombinators.iterate_succ_some
      (residualStep M S ss) hr
    exact .cons (entry_ordinary ((entry_step M S ss l hl v t).trans hs))
      (NondeterministicBlockSimulation.OrdinaryRun.of_iterate (residualStep M S ss) embed ordinary hr)

/-- A fixed syntax constant bounds the number of local transitions. -/
theorem compile_bounded (q : TM1.Stmt Γ Λ σ) (hq : some q∈TM1.stmts M S)
    (v : σ) (t : Tape Γ) :
    ∃ n d, 0<n ∧ n≤TM1PrimitiveTimeBounds.bound q ∧
      iter M S ss n (startResidual M S q hq v t)=some d ∧
      forgetCfg M S d=boundary (TM1.stepAux q v t) := by
  obtain ⟨d,hd,he⟩ := compile_exact M S ss q hq v t
  exact ⟨_,d,TM1PrimitiveTimeBounds.steps_pos q v t,TM1PrimitiveTimeBounds.steps_le q v t,hd,he⟩

omit ss in
/-- A Post-Turing command is a conventional write/move local action. -/
def commandAction (a : Γ) (q : State M S) : TM0.Stmt Γ →
    SingleTapeNondeterministic.Action Γ (State M S)
  | .move .left => ⟨a,.left,.run q⟩
  | .move .right => ⟨a,.right,.run q⟩
  | .write b => ⟨b,.stay,.run q⟩

omit ss in
def executeAction (a : SingleTapeNondeterministic.Action Γ (State M S)) (t : Tape Γ) :
    SingleTapeNondeterministic.Control (State M S) × Tape Γ :=
  (a.next,match a.motion with
    | .stay => t.write a.write
    | .left => (t.write a.write).move .left
    | .right => (t.write a.write).move .right)

omit ss [Inhabited Λ] in
theorem commandAction_correct (q : State M S) (s : TM0.Stmt Γ) (t : Tape Γ) :
    executeAction M S (commandAction M S t.head q s) t = (.run q,applyStmt s t) := by
  cases s with
  | move d => cases d <;> simp [executeAction,commandAction,applyStmt,Tape.write_self]
  | write a => rfl

/-- Every primitive is deterministic. The halt boundary returns `none` so that
its caller can provide a genuine local output checker. -/
noncomputable def instruction (q : State M S) (a : Γ) :
    Option (SingleTapeNondeterministic.Instruction Γ (State M S)) :=
  (transition M S ss q a).map fun (r,s) => .ordinary (commandAction M S a r s)

end Restriction

section Erasure
variable [Inhabited Λ] [Inhabited σ] (M : Λ → TM1.Stmt Γ Λ σ)

/-- Forget boundary labels exactly as mathlib's syntax compiler does. -/
def eraseState (q : RawState Γ Λ σ) : TM1to0.Λ' M :=
  (q.1.elim (fun l => some (M l)) id,q.2)

def eraseCfg (c : RawCfg Γ Λ σ) : TM0.Cfg Γ (TM1to0.Λ' M) :=
  ⟨eraseState M c.1,c.2⟩

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
theorem aux_erase (a : Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    Prod.map (eraseState M) id (aux a q v)=TM1to0.trAux M a q v := by
  induction q generalizing v with
  | move d q => rfl
  | write f q => rfl
  | load f q ih => exact ih _
  | branch f q r ihq ihr =>
    cases h : f a v <;> simp only [aux,TM1to0.trAux,h,Bool.false_eq_true,
      if_false,if_true,Bool.cond_false,Bool.cond_true]
    · exact ihr _
    · exact ihq _
  | goto f => rfl
  | halt => rfl

/-- One of our local transitions is exactly one mathlib primitive transition. -/
theorem rawStep_erase (c : RawCfg Γ Λ σ) :
    (rawStep M c).map (eraseCfg M)=TM0.step (TM1to0.tr M) (eraseCfg M c) := by
  rcases c with ⟨⟨l,v⟩,t⟩
  have he (q : TM1.Stmt Γ Λ σ) := congrArg
    (fun (r,s) => (⟨r,applyStmt s t⟩ : TM0.Cfg Γ (TM1to0.Λ' M))) (aux_erase M t.head q v)
  cases l with
  | inl l =>
    simpa [rawStep,rawTransition,eraseCfg,eraseState,TM0.step,TM1to0.tr,applyStmt] using congrArg some (he (M l))
  | inr q =>
    cases q with
    | none => rfl
    | some q =>
      simpa [rawStep,rawTransition,eraseCfg,eraseState,TM0.step,TM1to0.tr,applyStmt] using congrArg some (he q)

theorem step_erase (S : Finset Λ) (ss : TM1.Supports M S) (c : Cfg M S) :
    (step M S ss c).map (fun d => eraseCfg M (forgetCfg M S d)) =
      TM0.step (TM1to0.tr M) (eraseCfg M (forgetCfg M S c)) := by
  rw [←rawStep_erase,←step_forget M S ss,Option.map_map]
  rfl

end Erasure
end PlanarHom.TM1FiniteControl
