import PlanarHom.Complexity
import PlanarHom.StackTransfer
import PlanarHom.OracleAccounting
import Mathlib.Tactic.DeriveFintype

/-!
# Elimination of polynomial-time oracle subroutines

The compiler keeps the caller and callee in disjoint typed stack banks. Five
finite-control transfer loops copy a query, clear the old answer, and install the
callee's exact output. Every stack operation is genuine TM2 syntax.
-/

namespace PlanarHom.OracleSubstitution

noncomputable section

open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

theorem cfg_ext {K Λ σ : Type} {Γ : K → Type} {c d : Cfg Γ Λ σ}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl

inductive Phase | save | copy | clear | drain | restore
  deriving DecidableEq, Fintype

abbrev Bank (a b : FinTM2) := a.K ⊕ (b.K ⊕ Unit)
def Alphabet (a b : FinTM2) : Bank a b → Type :=
  Sum.elim a.Γ (Sum.elim b.Γ (fun _ => Bool))
abbrev Label (a b : FinTM2) := a.Λ ⊕ ((Phase × a.Λ) ⊕ (a.Λ × b.Λ))
abbrev State (a b : FinTM2) := (a.σ × b.σ) × Option Bool

def caller {a b : FinTM2} (l : a.Λ) : Label a b := .inl l
def phase {a b : FinTM2} (p : Phase) (l : a.Λ) : Label a b := .inr (.inl (p,l))
def callee {a b : FinTM2} (next : a.Λ) (l : b.Λ) : Label a b := .inr (.inr (next,l))
def temp {a b : FinTM2} : Bank a b := .inr (.inr ())

def callerEmbedding (a b : FinTM2) : StackEmbedding a.Γ (Alphabet a b) where
  index := ⟨Sum.inl, Sum.inl_injective⟩
  alphabet _ := Equiv.refl _
def calleeEmbedding (a b : FinTM2) : StackEmbedding b.Γ (Alphabet a b) where
  index := ⟨fun k => Sum.inr (Sum.inl k), by intro x y h; simpa using h⟩
  alphabet _ := Equiv.refl _

def callerState (a b : FinTM2) : (a.σ × (b.σ × Option Bool)) ≃ State a b :=
  (Equiv.prodAssoc _ _ _).symm

def calleeState (a b : FinTM2) : (b.σ × (a.σ × Option Bool)) ≃ State a b where
  toFun v := ((v.2.1,v.1),v.2.2)
  invFun v := (v.1.2,(v.1.1,v.2))
  left_inv _ := rfl
  right_inv _ := rfl

def callerStmt (a b : FinTM2) (q : a.Stmt) : Stmt (Alphabet a b) (Label a b) (State a b) :=
  renameState (callerState a b) (liftStmt (callerEmbedding a b) caller q)

def calleeStmt (a b : FinTM2) (next : a.Λ) (q : b.Stmt) :
    Stmt (Alphabet a b) (Label a b) (State a b) :=
  redirectHalt (phase .drain next)
    (renameState (calleeState a b) (liftStmt (calleeEmbedding a b) (callee next) q))

def store (a b : FinTM2) (A : ∀ k, List (a.Γ k)) (B : ∀ k, List (b.Γ k))
    (T : List Bool) : ∀ k, List (Alphabet a b k) :=
  fun | .inl k => A k | .inr (.inl k) => B k | .inr (.inr _) => T

@[simp] theorem store_left (a b : FinTM2) (A B T) (k : a.K) :
    store a b A B T (.inl k) = A k := rfl
@[simp] theorem store_right (a b : FinTM2) (A B T) (k : b.K) :
    store a b A B T (.inr (.inl k)) = B k := rfl
@[simp] theorem store_temp (a b : FinTM2) (A B T) :
    store a b A B T temp = T := rfl

def idle (a b : FinTM2) (c : a.Cfg) : Cfg (Alphabet a b) (Label a b) (State a b) :=
  ⟨c.l.map caller, ((c.var,b.initialState),none), store a b c.stk (fun _ => []) []⟩

def active (a b : FinTM2) (next : a.Λ) (v : a.σ) (A : ∀ k, List (a.Γ k))
    (c : b.Cfg) : Cfg (Alphabet a b) (Label a b) (State a b) :=
  ⟨(c.l.map (callee next)).or (some (phase .drain next)),
    ((v,c.var),none), store a b A c.stk []⟩

theorem callerStmt_correct (a b : FinTM2) (q : a.Stmt) (v : a.σ)
    (A : ∀ k, List (a.Γ k)) :
    stepAux (callerStmt a b q) ((v,b.initialState),none) (store a b A (fun _=>[]) []) =
      idle a b (stepAux q v A) := by
  let e := callerEmbedding a b
  have hs : e.RepresentsEmpty A (store a b A (fun _=>[]) []) := by
    constructor
    · intro k; change A k = (A k).map id; simp
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => cases k <;> rfl
  have h := liftStmt_correct_empty e (caller (a:=a) (b:=b)) q v (b.initialState,(none : Option Bool))
    A (store a b A (fun _=>[]) []) hs
  change stepAux (renameState (callerState a b) (liftStmt e caller q))
    ((callerState a b) (v,(b.initialState,none))) _ = _
  rw [renameState_correct]
  apply cfg_ext
  · exact h.1.1
  · exact congrArg (callerState a b) h.1.2.1
  · funext k
    cases k with
    | inl k =>
      have hh := h.2.1 k
      change _ = List.map id _ at hh
      simpa only [List.map_id] using hh
    | inr k =>
      have ht := h.2.2 (.inr k) (by intro j; simp [e, callerEmbedding])
      cases k <;> exact ht

theorem calleeStmt_correct (a b : FinTM2) (next : a.Λ) (q : b.Stmt)
    (v : a.σ) (w : b.σ) (A : ∀ k, List (a.Γ k)) (B : ∀ k, List (b.Γ k)) :
    stepAux (calleeStmt a b next q) ((v,w),none) (store a b A B []) =
      active a b next v A (stepAux q w B) := by
  let e := calleeEmbedding a b
  have hs : e.Represents B (store a b A B []) := by
    intro k; change B k = (B k).map id; simp
  have h := liftStmt_correct e (callee (a:=a) next) q w (v,(none : Option Bool)) B (store a b A B []) hs
  unfold calleeStmt
  rw [redirectHalt_correct]
  change continueCfg _ (stepAux (renameState (calleeState a b) (liftStmt e (callee next) q))
    ((calleeState a b) (w,(v,none))) _) = _
  rw [renameState_correct]
  apply cfg_ext
  · exact congrArg (fun l => l.or (some (phase .drain next))) h.1
  · exact congrArg (calleeState a b) h.2.1
  · funext k
    cases k with
    | inl k =>
      exact liftStmt_untouched e (callee next) q (w,(v,none)) _ (.inl k)
        (by intro j; simp [e, calleeEmbedding])
    | inr k =>
      cases k with
      | inl k =>
        have hh := h.2.2 k
        change _ = List.map id _ at hh
        simpa only [List.map_id] using hh
      | inr u =>
        exact liftStmt_untouched e (callee next) q (w,(v,none)) _ (.inr (.inr u))
          (by intro j; simp [e, calleeEmbedding])


def program (m : OracleTM2) (g : TM2ComputableAux Bool Bool) :
    Label m.core.tm g.tm → Stmt (Alphabet m.core.tm g.tm) (Label m.core.tm g.tm)
      (State m.core.tm g.tm)
  | .inl l => match m.request l with
    | none => callerStmt m.core.tm g.tm (m.core.tm.m l)
    | some next => .goto (fun _ => phase .save next)
  | .inr (.inl (.save,next)) => transferStmt (.inl m.queryStack) temp m.queryAlphabet id
      (phase .save next) (phase .copy next)
  | .inr (.inl (.copy,next)) => transfer₂Stmt temp (.inl m.queryStack) (.inr (.inl g.tm.k₀))
      id m.queryAlphabet.symm g.inputAlphabet.symm (phase .copy next) (phase .clear next)
  | .inr (.inl (.clear,next)) => clearStmt (.inl m.answerStack)
      (phase .clear next) (callee next g.tm.main)
  | .inr (.inl (.drain,next)) => transferStmt (.inr (.inl g.tm.k₁)) temp g.outputAlphabet id
      (phase .drain next) (phase .restore next)
  | .inr (.inl (.restore,next)) => transferStmt temp (.inl m.answerStack) id m.answerAlphabet.symm
      (phase .restore next) (caller next)
  | .inr (.inr (next,l)) => calleeStmt m.core.tm g.tm next (g.tm.m l)

/-- An explicit finite-control ordinary machine implementing every oracle call. -/
noncomputable def machine (m : OracleTM2) (g : TM2ComputableAux Bool Bool) : FinTM2 := by
  letI := m.core.tm.kFin
  letI := g.tm.kFin
  letI := m.core.tm.ΛFin
  letI := g.tm.ΛFin
  letI := m.core.tm.σFin
  letI := g.tm.σFin
  letI := m.core.tm.Γk₀Fin
  exact {
    K := Bank m.core.tm g.tm
    Γ := Alphabet m.core.tm g.tm
    k₀ := .inl m.core.tm.k₀
    k₁ := .inl m.core.tm.k₁
    Λ := Label m.core.tm g.tm
    main := caller m.core.tm.main
    σ := State m.core.tm g.tm
    initialState := ((m.core.tm.initialState,g.tm.initialState),none)
    Γk₀Fin := m.core.tm.Γk₀Fin
    m := program m g }

variable (m : OracleTM2) (g : TM2ComputableAux Bool Bool)

theorem ordinary_step (c d : m.Cfg) (hn : m.continuation c = none)
    (hs : m.core.tm.step c = some d) :
    (machine m g).step (idle m.core.tm g.tm c) = some (idle m.core.tm g.tm d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at hs
  | some l =>
    change m.request l = none at hn
    simp only [FinTM2.step,step,Option.some.injEq] at hs
    subst d
    change some (stepAux (program m g (caller l)) _ _) = _
    rw [show program m g (caller l) = callerStmt m.core.tm g.tm (m.core.tm.m l) by
      simp [program,caller,hn]]
    rw [callerStmt_correct]

theorem callee_step (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀ k, List (m.core.tm.Γ k)) (c d : g.tm.Cfg) (hs : g.tm.step c = some d) :
    (machine m g).step (active m.core.tm g.tm next v S c) =
      some (active m.core.tm g.tm next v S d) := by
  rcases c with ⟨l,w,B⟩
  cases l with
  | none => simp [FinTM2.step,step] at hs
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at hs
    subst d
    change some (stepAux (calleeStmt m.core.tm g.tm next (g.tm.m l)) _ _) = _
    rw [calleeStmt_correct]

/-- Runs of the supplied callee are embedded transition for transition while
all suspended caller stacks and its finite state are unchanged. -/
theorem callee_run (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀ k, List (m.core.tm.Γ k)) (c d : g.tm.Cfg) (n : ℕ)
    (hs : (fun x : Option g.tm.Cfg => x.bind g.tm.step)^[n] (some c) = some d) :
    (fun x : Option (machine m g).Cfg => x.bind (machine m g).step)^[n]
      (some (active m.core.tm g.tm next v S c)) =
        some (active m.core.tm g.tm next v S d) := by
  obtain ⟨e,he,hr⟩ := simulate_iterations g.tm.step (machine m g).step
    (fun c e => e = active m.core.tm g.tm next v S c)
    (by intro c d e hs he; subst e; exact ⟨_,callee_step m g next v S c d hs,rfl⟩)
    c d (active m.core.tm g.tm next v S c) n hs rfl
  simpa [hr] using he


theorem store_update_left (a b : FinTM2) (A B T) (k : a.K) (xs : List (a.Γ k)) :
    Function.update (store a b A B T) (.inl k) xs =
      store a b (Function.update A k xs) B T := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inl_injective.ne h)]
  | inr j => cases j <;> simp [store, Function.update_of_ne]

theorem store_update_right (a b : FinTM2) (A B T) (k : b.K) (xs : List (b.Γ k)) :
    Function.update (store a b A B T) (.inr (.inl k)) xs =
      store a b A (Function.update B k xs) T := by
  funext j
  cases j with
  | inl j => simp [store, Function.update_of_ne]
  | inr j =>
    cases j with
    | inl j =>
      by_cases h : j = k
      · subst j; simp
      · simp [Function.update_of_ne h, Function.update_of_ne
          (Sum.inr_injective.ne (Sum.inl_injective.ne h))]
    | inr u => simp [store, Function.update_of_ne]

theorem store_update_temp (a b : FinTM2) (A B T) (xs : List Bool) :
    Function.update (store a b A B T) temp xs = store a b A B xs := by
  funext j
  cases j with
  | inl j => simp [store, temp, Function.update_of_ne]
  | inr j => cases j with
    | inl j => simp [store, temp, Function.update_of_ne]
    | inr u => cases u; simp [temp,store]

def stage (p : Phase) (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k, List (m.core.tm.Γ k)) (B : ∀ k, List (g.tm.Γ k)) (T : Bits) :
    (machine m g).Cfg :=
  ⟨some (phase p next),((v,g.tm.initialState),none),store m.core.tm g.tm A B T⟩

abbrev iter (n : ℕ) (c : (machine m g).Cfg) : Option (machine m g).Cfg :=
  (fun x : Option (machine m g).Cfg => x.bind (machine m g).step)^[n] (some c)

theorem iter_trans {n k : ℕ} {c d e : (machine m g).Cfg}
    (h : iter m g n c = some d) (h' : iter m g k d = some e) :
    iter m g (k+n) c = some e := by
  unfold iter at *
  rw [Function.iterate_add_apply,h]
  exact h'

theorem entry_run (c : m.Cfg) (next : m.core.tm.Λ)
    (hq : m.continuation c = some next) :
    iter m g 1 (idle m.core.tm g.tm c) =
      some (stage m g .save next c.var c.stk (fun _=>[]) []) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [OracleTM2.continuation] at hq
  | some l =>
    change m.request l = some next at hq
    simp [iter,idle,stage,machine,program,caller,hq,FinTM2.step,step,stepAux]

theorem save_run (next : m.core.tm.Λ) (v : m.core.tm.σ) (A : ∀ k,List (m.core.tm.Γ k)) :
    iter m g ((A m.queryStack).length+1)
      (stage m g .save next v A (fun _=>[]) []) =
    some (stage m g .copy next v (Function.update A m.queryStack []) (fun _=>[])
      ((A m.queryStack).map m.queryAlphabet).reverse) := by
  have h := transfer_run (program m g) (.inl m.queryStack) temp (by simp [temp])
    m.queryAlphabet id (phase .save next) (phase .copy next) rfl
    (v,g.tm.initialState) none (store m.core.tm g.tm A (fun _=>[]) [])
  simpa [iter,stage,machine,FinTM2.step,transferStore,store_update_left,store_update_temp,
    Function.comp_def] using h

theorem copy_run (next : m.core.tm.Λ) (v : m.core.tm.σ) (A : ∀ k,List (m.core.tm.Γ k)) :
    iter m g ((A m.queryStack).length+1)
      (stage m g .copy next v (Function.update A m.queryStack []) (fun _=>[])
        ((A m.queryStack).map m.queryAlphabet).reverse) =
    some (stage m g .clear next v A
      (pointStack g.tm.k₀ (((A m.queryStack).map m.queryAlphabet).map g.inputAlphabet.symm)) []) := by
  have h := transfer₂_run (program m g) temp (.inl m.queryStack) (.inr (.inl g.tm.k₀))
    (by simp [temp]) (by simp [temp]) (by simp)
    id m.queryAlphabet.symm g.inputAlphabet.symm (phase .copy next) (phase .clear next) rfl
    (v,g.tm.initialState) none
    (store m.core.tm g.tm (Function.update A m.queryStack []) (fun _=>[])
      ((A m.queryStack).map m.queryAlphabet).reverse)
  simpa [iter,stage,machine,FinTM2.step,transfer₂Store,transferStore,store_update_left,
    store_update_right,store_update_temp,Function.comp_def,pointStack,
    List.map_reverse,List.map_map,Function.update_eq_self] using h

theorem clear_run' (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (q : Bits) :
    iter m g ((A m.answerStack).length+1)
      (stage m g .clear next v A (pointStack g.tm.k₀ (q.map g.inputAlphabet.symm)) []) =
    some (active m.core.tm g.tm next v (Function.update A m.answerStack [])
      (initList g.tm (q.map g.inputAlphabet.symm))) := by
  have h := clear_run (program m g) (.inl m.answerStack)
    (phase .clear next) (callee next g.tm.main) rfl
    (v,g.tm.initialState) none
    (store m.core.tm g.tm A (pointStack g.tm.k₀ (q.map g.inputAlphabet.symm)) [])
  simpa [iter,stage,machine,FinTM2.step,store_update_left,active,initList_stk] using h

theorem drain_run (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (answer : Bits) :
    iter m g (answer.length+1)
      (active m.core.tm g.tm next v A (haltList g.tm (answer.map g.outputAlphabet.symm))) =
    some (stage m g .restore next v A (fun _=>[]) answer.reverse) := by
  have h := transfer_run (program m g) (.inr (.inl g.tm.k₁)) temp (by simp [temp])
    g.outputAlphabet id (phase .drain next) (phase .restore next) rfl
    (v,g.tm.initialState) none
    (store m.core.tm g.tm A (pointStack g.tm.k₁ (answer.map g.outputAlphabet.symm)) [])
  simpa [iter,stage,machine,FinTM2.step,active,haltList_stk,
    transferStore,store_update_right,store_update_temp,pointStack,
    Function.comp_def,List.map_map,Function.update_eq_self] using h

theorem restore_run (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (answer : Bits) :
    iter m g (answer.length+1)
      (stage m g .restore next v (Function.update A m.answerStack []) (fun _=>[]) answer.reverse) =
    some (idle m.core.tm g.tm ⟨some next,v,
      Function.update A m.answerStack (answer.map m.answerAlphabet.symm)⟩) := by
  have h := transfer_run (program m g) temp (.inl m.answerStack) (by simp [temp])
    id m.answerAlphabet.symm (phase .restore next) (caller next) rfl
    (v,g.tm.initialState) none
    (store m.core.tm g.tm (Function.update A m.answerStack []) (fun _=>[]) answer.reverse)
  simpa [iter,stage,machine,FinTM2.step,idle,transferStore,store_update_temp,
    store_update_left,Function.comp_def,List.map_reverse] using h

/-- A complete call protocol, with an exact actual-transition count. The caller
may query repeatedly, its query/answer stacks may coincide, and every other
caller stack is preserved verbatim. -/
theorem query_run_exact (oracle : Bits → Bits) (c : m.Cfg) (next : m.core.tm.Λ)
    (hq : m.continuation c = some next) (t : ℕ)
    (out : TM2OutputsInTime g.tm ((m.queryWord c).map g.inputAlphabet.symm)
      (some ((oracle (m.queryWord c)).map g.outputAlphabet.symm)) t) :
    iter m g (6 + (c.stk m.answerStack).length + 2*(m.queryWord c).length +
      2*(oracle (m.queryWord c)).length + out.steps) (idle m.core.tm g.tm c) =
    some (idle m.core.tm g.tm (m.answerCfg oracle c next)) := by
  have h₁ := iter_trans m g (entry_run m g c next hq) (save_run m g next c.var c.stk)
  have h₂ := iter_trans m g h₁ (copy_run m g next c.var c.stk)
  have h₃ := iter_trans m g h₂ (clear_run' m g next c.var c.stk (m.queryWord c))
  have h₄ := iter_trans m g h₃ (callee_run m g next c.var (Function.update c.stk m.answerStack [])
    _ _ out.steps out.evals_in_steps)
  have h₅ := iter_trans m g h₄ (drain_run m g next c.var
    (Function.update c.stk m.answerStack []) (oracle (m.queryWord c)))
  have h₆ := iter_trans m g h₅ (restore_run m g next c.var c.stk (oracle (m.queryWord c)))
  convert h₆ using 1
  simp only [OracleTM2.queryWord,List.length_map]
  congr 1
  omega

/-- The concrete compiled call has the transfer overhead plus the callee's
proved running time, rather than a unit-cost application of a Lean function. -/
theorem query_run (oracle : Bits → Bits) (p : Polynomial ℕ)
    (outputs : ∀ q : Bits, TM2OutputsInTime g.tm (q.map g.inputAlphabet.symm)
      (some ((oracle q).map g.outputAlphabet.symm)) (p.eval q.length))
    (c : m.Cfg) (next : m.core.tm.Λ) (hq : m.continuation c = some next) :
    ∃ n, n ≤ 6 + (c.stk m.answerStack).length + 2*(m.queryWord c).length +
      2*(oracle (m.queryWord c)).length + p.eval (m.queryWord c).length ∧
      iter m g n (idle m.core.tm g.tm c) =
        some (idle m.core.tm g.tm (m.answerCfg oracle c next)) := by
  let out := outputs (m.queryWord c)
  refine ⟨_,Nat.add_le_add_left out.steps_le_m _,query_run_exact m g oracle c next hq _ out⟩

@[simp] theorem store_empty (a b : FinTM2) :
    store a b (fun _=>[]) (fun _=>[]) [] = (fun _=>[]) := by
  funext k; cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem idle_initial (x : Bits) :
    idle m.core.tm g.tm (m.initial x) =
      initList (machine m g) (x.map m.core.inputAlphabet.symm) := by
  apply cfg_ext
  · rfl
  · rfl
  · change store m.core.tm g.tm (initList m.core.tm _).stk (fun _=>[]) [] = _
    rw [initList_stk,initList_stk]
    change store m.core.tm g.tm (pointStack m.core.tm.k₀ _) (fun _=>[]) [] =
      pointStack (.inl m.core.tm.k₀) _
    simp only [pointStack,←store_update_left,store_empty]

theorem idle_final (x : Bits) :
    idle m.core.tm g.tm (m.final x) =
      haltList (machine m g) (x.map m.core.outputAlphabet.symm) := by
  apply cfg_ext
  · rfl
  · rfl
  · change store m.core.tm g.tm (haltList m.core.tm _).stk (fun _=>[]) [] = _
    rw [haltList_stk,haltList_stk]
    change store m.core.tm g.tm (pointStack m.core.tm.k₁ _) (fun _=>[]) [] =
      pointStack (.inl m.core.tm.k₁) _
    simp only [pointStack,←store_update_left,store_empty]

/-- The compiler introduces no infinite stack alphabets: it retains each source
alphabet and adds only the Boolean transfer stack. -/
def alphabetFintype [∀ k, Fintype (g.tm.Γ k)] : ∀ k, Fintype ((machine m g).Γ k)
  | .inl k => m.finiteAlphabet k
  | .inr (.inl k) => inferInstanceAs (Fintype (g.tm.Γ k))
  | .inr (.inr _) => inferInstanceAs (Fintype Bool)

/-- Every finite oracle run is simulated by the constructed ordinary machine.
The bound is cumulative over all calls, including copying and clearing costs. -/
theorem compiled_run {oracle : Bits → Bits} (p : Polynomial ℕ)
    (outputs : ∀ q : Bits, TM2OutputsInTime g.tm (q.map g.inputAlphabet.symm)
      (some ((oracle q).map g.outputAlphabet.symm)) (p.eval q.length))
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle c d steps cost qs) (N : ℕ)
    (hN : ∀ k, (c.stk k).length ≤ N) :
    ∃ n, n ≤ cost * (6 + N + (machinePushBound m.core.tm + 5) * cost + p.eval cost) ∧
      iter m g n (idle m.core.tm g.tm c) = some (idle m.core.tm g.tm d) :=
  hr.replacement_bound p (machine m g).step (idle m.core.tm g.tm)
    (ordinary_step m g) (query_run m g oracle p outputs) N hN

/-- The caller's polynomial is multiplied by a polynomial upper bound on each
complete replaced transition, evaluated at the caller's charged-time bound. -/
def timePolynomial (m : OracleTM2) (callerTime calleeTime : Polynomial ℕ) : Polynomial ℕ :=
  callerTime * (Polynomial.C 6 + Polynomial.X +
    Polynomial.C (machinePushBound m.core.tm + 5) * callerTime + calleeTime.comp callerTime)

/-- The actual oracle-subroutine substitution compiler. No semantic compiler
hypothesis, infinite control state, or unfinished mathlib composition result is
used. Its output is mathlib's original exact-output polynomial-time TM2 witness. -/
def substituteComputer {target oracle : Bits → Bits}
    (r : PolyTimeTuringReduction target oracle)
    (h : TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      BitEncoding.bits.toFinEncoding oracle) :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      BitEncoding.bits.toFinEncoding target := by
  let g : TM2ComputableAux Bool Bool := h.toTM2ComputableAux
  refine {
    tm := machine r.machine g
    inputAlphabet := r.machine.core.inputAlphabet
    outputAlphabet := r.machine.core.outputAlphabet
    time := timePolynomial r.machine r.time h.time
    outputsFun := ?_ }
  intro x
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost⟩ := r.computes x
  have hN : ∀ k, ((r.machine.initial x).stk k).length ≤ x.length := by
    intro k
    simp only [OracleTM2.initial,initList]
    split
    · rename_i hk; subst k; simp
    · simp
  have outputs : ∀ q : Bits, TM2OutputsInTime g.tm (q.map g.inputAlphabet.symm)
      (some ((oracle q).map g.outputAlphabet.symm)) (h.time.eval q.length) :=
    fun q => h.outputsFun q
  obtain ⟨n,hn,he⟩ := compiled_run r.machine g h.time outputs hr x.length hN
  refine ⟨{
    steps := n
    steps_le_m := ?_
    evals_in_steps := ?_ }⟩
  · rw [idle_initial,idle_final] at he
    exact he
  · apply hn.trans
    have hi : 6 + x.length + (machinePushBound r.machine.core.tm + 5) * cost +
        h.time.eval cost ≤ 6 + x.length +
        (machinePushBound r.machine.core.tm + 5) * r.time.eval x.length +
        h.time.eval (r.time.eval x.length) :=
      Nat.add_le_add (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ hcost) _) (natPolynomial_monotone h.time hcost)
    have hh := Nat.mul_le_mul hcost hi
    simpa [timePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp] using hh

end

end PlanarHom.OracleSubstitution

namespace PlanarHom.Complexity

/-- Polynomial-time Turing reductions preserve actual FP, by the fully proved
oracle-subroutine compiler and its cumulative polynomial running-time bound. -/
theorem PolyTimeTuringReduction.fp {target oracle : Bits → Bits}
    (r : PolyTimeTuringReduction target oracle)
    (h : FP BitEncoding.bits BitEncoding.bits oracle) :
    FP BitEncoding.bits BitEncoding.bits target := by
  obtain ⟨computer⟩ := h
  exact ⟨OracleSubstitution.substituteComputer r computer⟩

theorem TuringReduces.fp {target oracle : Bits → Bits}
    (r : TuringReduces target oracle) (h : FP BitEncoding.bits BitEncoding.bits oracle) :
    FP BitEncoding.bits BitEncoding.bits target := by
  obtain ⟨reduction⟩ := r
  exact reduction.fp h

end PlanarHom.Complexity
