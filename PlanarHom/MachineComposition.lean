import Mathlib.Computability.TMComputable
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

/-!
# Typed TM2 compiler foundations

These constructions recurse over actual TM2 syntax. They do not use the unfinished
`TM2ComputableInPolyTime.comp` declaration.
-/

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K J Λ Μ σ τ : Type} {Γ : K → Type} {Δ : J → Type}

/-- A typed, injective embedding of source stacks into destination stacks. -/
structure StackEmbedding (Γ : K → Type) (Δ : J → Type) where
  index : K ↪ J
  alphabet : ∀ k, Γ k ≃ Δ (index k)

namespace StackEmbedding

variable (e : StackEmbedding Γ Δ)

/-- The source stacks are represented symbol for symbol in the selected target stacks. -/
def Represents (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) : Prop :=
  ∀ k, T (e.index k) = (S k).map (e.alphabet k)

@[simp] theorem represents_empty : e.Represents (fun _ => []) (fun _ => []) := by
  intro k
  rfl

theorem represents_update [DecidableEq K] [DecidableEq J]
    {S : ∀ k, List (Γ k)} {T : ∀ j, List (Δ j)}
    (h : e.Represents S T) (k : K) (xs : List (Γ k)) :
    e.Represents (Function.update S k xs)
      (Function.update T (e.index k) (xs.map (e.alphabet k))) := by
  intro k'
  by_cases hk : k' = k
  · subst k'
    simp
  · have hj : e.index k' ≠ e.index k := fun h => hk (e.index.injective h)
    simpa [Function.update_of_ne hk, Function.update_of_ne hj] using h k'

end StackEmbedding

/-- Compile stack operations through a typed embedding, rename labels, and carry
an untouched extra finite-control register. `halt` is retained as an actual halt. -/
def liftStmt (e : StackEmbedding Γ Δ) (labels : Λ → Μ) :
    Stmt Γ Λ σ → Stmt Δ Μ (σ × τ)
  | .push k f q => .push (e.index k) (fun v => e.alphabet k (f v.1)) (liftStmt e labels q)
  | .peek k f q => .peek (e.index k)
      (fun v a => (f v.1 (a.map (e.alphabet k).symm), v.2)) (liftStmt e labels q)
  | .pop k f q => .pop (e.index k)
      (fun v a => (f v.1 (a.map (e.alphabet k).symm), v.2)) (liftStmt e labels q)
  | .load f q => .load (fun v => (f v.1, v.2)) (liftStmt e labels q)
  | .branch f q r => .branch (fun v => f v.1) (liftStmt e labels q) (liftStmt e labels r)
  | .goto f => .goto (fun v => labels (f v.1))
  | .halt => .halt

/-- Configuration simulation relation, with exact label and finite-state behavior. -/
def Represents (e : StackEmbedding Γ Δ) (labels : Λ → Μ) (extra : τ)
    (a : Cfg Γ Λ σ) (b : Cfg Δ Μ (σ × τ)) : Prop :=
  b.l = a.l.map labels ∧ b.var = (a.var, extra) ∧ e.Represents a.stk b.stk

/-- One complete compiled statement simulates exactly one source statement.
No input-dependent unbounded operation is introduced. -/
theorem liftStmt_correct [DecidableEq K] [DecidableEq J]
    (e : StackEmbedding Γ Δ) (labels : Λ → Μ) (q : Stmt Γ Λ σ)
    (v : σ) (extra : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j))
    (h : e.Represents S T) :
    Represents e labels extra (stepAux q v S)
      (stepAux (liftStmt e labels q) (v, extra) T) := by
  induction q generalizing v S T with
  | push k f q ih =>
      simp only [liftStmt, stepAux]
      apply ih
      simpa [h k] using e.represents_update h k (f v :: S k)
  | peek k f q ih =>
      simp only [liftStmt, stepAux]
      have hh : ((T (e.index k)).head?).map (e.alphabet k).symm = (S k).head? := by
        rw [h k, List.head?_map, Option.map_map]
        simp
      rw [hh]
      exact ih _ _ _ h
  | pop k f q ih =>
      simp only [liftStmt, stepAux]
      have hh : ((T (e.index k)).head?).map (e.alphabet k).symm = (S k).head? := by
        rw [h k, List.head?_map, Option.map_map]
        simp
      rw [hh]
      apply ih
      simpa [h k] using e.represents_update h k (S k).tail
  | load f q ih =>
      simpa only [liftStmt, stepAux] using ih (f v) S T h
  | branch f q r ihq ihr =>
      cases hf : f v <;> simp only [liftStmt, stepAux, hf, Bool.cond_false, Bool.cond_true]
      · exact ihr _ _ _ h
      · exact ihq _ _ _ h
  | goto f => exact ⟨rfl, rfl, h⟩
  | halt => exact ⟨rfl, rfl, h⟩

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K J Λ Μ σ τ : Type} {Γ : K → Type} {Δ : J → Type}

/-- Transport finite control through an equivalence, without touching the stacks. -/
def renameState (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ
  | .push k f q => .push k (fun v => f (e.symm v)) (renameState e q)
  | .peek k f q => .peek k (fun v a => e (f (e.symm v) a)) (renameState e q)
  | .pop k f q => .pop k (fun v a => e (f (e.symm v) a)) (renameState e q)
  | .load f q => .load (fun v => e (f (e.symm v))) (renameState e q)
  | .branch f q r => .branch (fun v => f (e.symm v)) (renameState e q) (renameState e r)
  | .goto f => .goto (fun v => f (e.symm v))
  | .halt => .halt

/-- Transport a configuration's finite control through an equivalence. -/
def renameCfgState (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

theorem renameState_correct [DecidableEq K] (e : σ ≃ τ) (q : Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux (renameState e q) (e v) S = renameCfgState e (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa [renameState] using ih v (Function.update S k (f v :: S k))
  | peek k f q ih => simpa [renameState] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simpa [renameState] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => simpa [renameState] using ih (f v) S
  | branch f q r ihq ihr =>
      cases hf : f v <;> simp [renameState, hf, ihq, ihr]
  | goto f => simp [renameState, renameCfgState]
  | halt => rfl

/-- Replace every terminal instruction by a jump to a fixed continuation. -/
def redirectHalt (next : Λ) : Stmt Γ Λ σ → Stmt Γ Λ σ
  | .push k f q => .push k f (redirectHalt next q)
  | .peek k f q => .peek k f (redirectHalt next q)
  | .pop k f q => .pop k f (redirectHalt next q)
  | .load f q => .load f (redirectHalt next q)
  | .branch f q r => .branch f (redirectHalt next q) (redirectHalt next r)
  | .goto f => .goto f
  | .halt => .goto (fun _ => next)

/-- Only the terminal program counter is changed by continuation wiring. -/
def continueCfg (next : Λ) (c : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  { c with l := c.l.or (some next) }

theorem redirectHalt_correct [DecidableEq K] (next : Λ) (q : Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux (redirectHalt next q) v S = continueCfg next (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
      cases hf : f v <;> simp [redirectHalt, hf, ihq, ihr]
  | goto f => rfl
  | halt => rfl

/-- A compiled source instruction cannot alter any stack outside its bank. -/
theorem liftStmt_untouched [DecidableEq J]
    (e : StackEmbedding Γ Δ) (labels : Λ → Μ) (q : Stmt Γ Λ σ)
    (v : σ × τ) (T : ∀ j, List (Δ j)) (j : J)
    (hj : ∀ k, j ≠ e.index k) :
    (stepAux (liftStmt e labels q) v T).stk j = T j := by
  induction q generalizing v T with
  | push k f q ih =>
      simpa only [liftStmt, stepAux, Function.update_of_ne (hj k)] using
        ih v (Function.update T (e.index k) (e.alphabet k (f v.1) :: T (e.index k)))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      simpa only [liftStmt, stepAux, Function.update_of_ne (hj k)] using
        ih _ (Function.update T (e.index k) (T (e.index k)).tail)
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
      cases hf : f v.1 <;> simp only [liftStmt, stepAux, hf, Bool.cond_false, Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => rfl
  | halt => rfl

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K Λ σ : Type} {Γ : K → Type}

/-- A syntax-derived bound on pushes in one instruction. Counting both branches
is deliberately conservative and is independent of the input. -/
def pushBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => pushBound q + pushBound r
  | .goto _ => 0
  | .halt => 0

/-- Every output stack grows by at most the fixed instruction's push bound. -/
theorem stepAux_length_le [DecidableEq K] (q : Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (n : ℕ) (h : ∀ k, (S k).length ≤ n) :
    ∀ k, ((stepAux q v S).stk k).length ≤ n + pushBound q := by
  induction q generalizing v S n with
  | push j f q ih =>
      intro k
      have hu : ∀ k, ((Function.update S j (f v :: S j)) k).length ≤ n + 1 := by
        intro k
        by_cases hk : k = j
        · subst k; simpa using Nat.add_le_add_right (h j) 1
        · simp [Function.update_of_ne hk]; exact (h k).trans (Nat.le_add_right _ _)
      have := ih v _ (n + 1) hu k
      simpa [pushBound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | peek j f q ih => exact ih _ _ _ h
  | pop j f q ih =>
      intro k
      apply ih _ _ _ _ k
      intro k
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, List.length_tail]; have := h j; omega
      · simpa [Function.update_of_ne hk] using h k
  | load f q ih => exact ih _ _ _ h
  | branch f q r ihq ihr =>
      intro k
      cases hf : f v
      · simpa [stepAux, hf, pushBound] using
          (ihr v S n h k).trans (Nat.add_le_add_left (Nat.le_add_left _ _) n)
      · simpa [stepAux, hf, pushBound] using
          (ihq v S n h k).trans (Nat.add_le_add_left (Nat.le_add_right _ _) n)
  | goto f => simpa [pushBound] using h
  | halt => simpa [pushBound] using h

/-- A uniform one-step bound, extracted from the finite program text. -/
noncomputable def machinePushBound (tm : FinTM2) : ℕ :=
  @Finset.sum tm.Λ ℕ _ (@Finset.univ tm.Λ tm.ΛFin) (fun l => pushBound (tm.m l))

theorem step_length_le (tm : FinTM2) {a b : tm.Cfg} (hstep : tm.step a = some b)
    (n : ℕ) (h : ∀ k, (a.stk k).length ≤ n) :
    ∀ k, (b.stk k).length ≤ n + machinePushBound tm := by
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [FinTM2.step, step] at hstep
  | some l =>
      simp only [FinTM2.step, step, Option.some.injEq] at hstep
      subst b
      intro k
      apply (stepAux_length_le (tm.m l) v S n h k).trans
      apply Nat.add_le_add_left
      letI := tm.ΛFin
      exact Finset.single_le_sum (f := fun l => pushBound (tm.m l))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

/-- The actual step iterator has a linear bound on every materialized stack. -/
theorem iterate_length_le (tm : FinTM2) (a b : tm.Cfg) (steps n : ℕ)
    (h : (flip bind tm.step)^[steps] (some a) = some b)
    (ha : ∀ k, (a.stk k).length ≤ n) :
    ∀ k, (b.stk k).length ≤ n + steps * machinePushBound tm := by
  change (fun x : Option tm.Cfg => x.bind tm.step)^[steps] (some a) = some b at h
  induction steps generalizing b with
  | zero =>
      have hab : a = b := Option.some.inj h
      subst b
      simpa using ha
  | succ steps ih =>
      rw [Function.iterate_succ_apply'] at h
      cases hc : (fun x : Option tm.Cfg => x.bind tm.step)^[steps] (some a) with
      | none => rw [hc] at h; cases h
      | some c =>
          rw [hc] at h
          change tm.step c = some b at h
          have hb := step_length_le tm h (n + steps * machinePushBound tm) (ih c hc)
          simpa [Nat.succ_mul, Nat.add_assoc] using hb

/-- Exact-output computations cannot produce an uncharged, arbitrarily long word. -/
theorem outputs_length_le (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (n : ℕ)
    (h : TM2OutputsInTime tm input (some output) n) :
    output.length ≤ input.length + n * machinePushBound tm := by
  have ha : ∀ k, ((initList tm input).stk k).length ≤ input.length := by
    intro k
    simp only [initList]
    split
    · rename_i hk; subst k; simp
    · simp
  have hh := iterate_length_le tm (initList tm input) (haltList tm output)
    h.steps input.length h.evals_in_steps ha tm.k₁
  simp only [haltList] at hh
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Computability Polynomial

/-- A polynomial output-length bound extracted from the machine and its proved
running-time polynomial. It uses the fixed finite syntax, not a unit-cost output. -/
noncomputable def outputLengthPolynomial {α β : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    Polynomial ℕ := X + C (machinePushBound h.tm) * h.time

theorem encoded_output_length_le {α β : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb.encode (f a)).length ≤ (outputLengthPolynomial h).eval (ea.encode a).length := by
  have hh := outputs_length_le h.tm _ _ _ (h.outputsFun a)
  simpa [outputLengthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm] using hh

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K J Λ Μ σ τ : Type} {Γ : K → Type} {Δ : J → Type}

/-- Two stack banks, identifying exactly the first output with the second input.
This avoids copying (and reversing) an intermediate word. -/
abbrev SharedBank (out : K) (J : Type) := { k : K // k ≠ out } ⊕ J

/-- Each unshared stack keeps its original dependent alphabet. -/
def sharedAlphabet (out : K) (Γ : K → Type) (Δ : J → Type) : SharedBank out J → Type :=
  Sum.elim (fun k => Γ k.val) Δ

/-- The first bank's distinguished stack is represented by the second input stack. -/
def leftIndex [DecidableEq K] (out : K) (input : J) (k : K) : SharedBank out J :=
  if h : k = out then .inr input else .inl ⟨k, h⟩

theorem leftIndex_injective [DecidableEq K] (out : K) (input : J) :
    Function.Injective (leftIndex out input) := by
  intro k k' h
  by_cases hk : k = out <;> by_cases hk' : k' = out
  · exact hk.trans hk'.symm
  · simp [leftIndex, hk, hk'] at h
  · simp [leftIndex, hk, hk'] at h
  · simpa [leftIndex, hk, hk'] using h

/-- Typed first-bank embedding. Only the shared stack's alphabet is converted. -/
def leftEmbedding [DecidableEq K] (out : K) (input : J) (alphabet : Γ out ≃ Δ input) :
    StackEmbedding Γ (sharedAlphabet out Γ Δ) where
  index := ⟨leftIndex out input, leftIndex_injective out input⟩
  alphabet k := by
    by_cases hk : k = out
    · subst k
      simpa [leftIndex, sharedAlphabet] using alphabet
    · simpa [leftIndex, sharedAlphabet, hk] using Equiv.refl (Γ k)

/-- The second bank is a literal typed subfamily of the destination banks. -/
def rightEmbedding (out : K) (Γ : K → Type) (Δ : J → Type) :
    StackEmbedding Δ (sharedAlphabet out Γ Δ) where
  index := ⟨Sum.inr, Sum.inr_injective⟩
  alphabet _ := Equiv.refl _

/-- Explicit sequential composition of finite-control TM2 programs.
The output/input stack is shared through the given alphabet equivalence. -/
noncomputable def sequentialMachine (a b : FinTM2)
    (alphabet : a.Γ a.k₁ ≃ b.Γ b.k₀) : FinTM2 := by
  letI := a.kFin
  letI := a.Γk₀Fin
  letI := b.kFin
  letI := a.ΛFin
  letI := b.ΛFin
  letI := a.σFin
  letI := b.σFin
  let e := leftEmbedding a.k₁ b.k₀ alphabet
  let r := rightEmbedding a.k₁ a.Γ b.Γ
  exact {
    K := SharedBank a.k₁ b.K
    k₀ := e.index a.k₀
    k₁ := Sum.inr b.k₁
    Γ := sharedAlphabet a.k₁ a.Γ b.Γ
    Λ := a.Λ ⊕ b.Λ
    main := Sum.inl a.main
    σ := a.σ × b.σ
    initialState := (a.initialState, b.initialState)
    Γk₀Fin := Fintype.ofEquiv (a.Γ a.k₀) (e.alphabet a.k₀)
    m := Sum.elim
      (fun l => redirectHalt (Sum.inr b.main) (liftStmt e Sum.inl (a.m l)))
      (fun l => renameState (Equiv.prodComm b.σ a.σ) (liftStmt r Sum.inr (b.m l))) }

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

/-- Exact finite-run simulation for genuine partial transition functions.
The premise concerns each real source transition, not abstract function application. -/
theorem simulate_iterations {A B : Type} (f : A → Option A) (g : B → Option B)
    (R : A → B → Prop)
    (sim : ∀ a a' b, f a = some a' → R a b → ∃ b', g b = some b' ∧ R a' b')
    (a a' : A) (b : B) (n : ℕ)
    (h : (fun x : Option A => x.bind f)^[n] (some a) = some a') (hr : R a b) :
    ∃ b', (fun x : Option B => x.bind g)^[n] (some b) = some b' ∧ R a' b' := by
  induction n generalizing a' with
  | zero =>
      have haa : a = a' := Option.some.inj h
      subst a'
      exact ⟨b, rfl, hr⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h
      cases hc : (fun x : Option A => x.bind f)^[n] (some a) with
      | none => rw [hc] at h; cases h
      | some c =>
          rw [hc] at h
          change f c = some a' at h
          obtain ⟨d, hd, hcd⟩ := ih c hc
          obtain ⟨d', hd', hcd'⟩ := sim c a' d h hcd
          exact ⟨d', by rw [Function.iterate_succ_apply', hd]; exact hd', hcd'⟩

variable {K J Λ Μ σ τ : Type} {Γ : K → Type} {Δ : J → Type}

namespace StackEmbedding

/-- In addition to symbol-for-symbol representation, all unowned stacks are empty. -/
def RepresentsEmpty (e : StackEmbedding Γ Δ)
    (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) : Prop :=
  e.Represents S T ∧ ∀ j, (∀ k, j ≠ e.index k) → T j = []

theorem representsEmpty_unique (e : StackEmbedding Γ Δ)
    {S : ∀ k, List (Γ k)} {T U : ∀ j, List (Δ j)}
    (hT : e.RepresentsEmpty S T) (hU : e.RepresentsEmpty S U) : T = U := by
  classical
  funext j
  by_cases hj : ∃ k, e.index k = j
  · obtain ⟨k, rfl⟩ := hj
    exact (hT.1 k).trans (hU.1 k).symm
  · have he : ∀ k, j ≠ e.index k := by simpa [eq_comm] using hj
    exact (hT.2 j he).trans (hU.2 j he).symm

end StackEmbedding

/-- The embedding proof also accounts for every stack outside the active bank. -/
theorem liftStmt_correct_empty [DecidableEq K] [DecidableEq J]
    (e : StackEmbedding Γ Δ) (labels : Λ → Μ) (q : Stmt Γ Λ σ)
    (v : σ) (extra : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j))
    (h : e.RepresentsEmpty S T) :
    Represents e labels extra (stepAux q v S)
      (stepAux (liftStmt e labels q) (v, extra) T) ∧
      e.RepresentsEmpty (stepAux q v S).stk
        (stepAux (liftStmt e labels q) (v, extra) T).stk := by
  have hr := liftStmt_correct e labels q v extra S T h.1
  refine ⟨hr, hr.2.2, ?_⟩
  intro j hj
  exact (liftStmt_untouched e labels q (v, extra) T j hj).trans (h.2 j hj)

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K J : Type} {Γ : K → Type} {Δ : J → Type}

/-- A stack store with one materialized word and every other stack empty. -/
def pointStack [DecidableEq K] (k : K) (xs : List (Γ k)) : ∀ j, List (Γ j) :=
  Function.update (fun _ => []) k xs

@[simp] theorem initList_stk (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    (initList tm xs).stk = pointStack tm.k₀ xs := by
  funext k
  by_cases hk : k = tm.k₀
  · subst k; simp [initList, pointStack]
  · simp [initList, pointStack, hk]

@[simp] theorem haltList_stk (tm : FinTM2) (xs : List (tm.Γ tm.k₁)) :
    (haltList tm xs).stk = pointStack tm.k₁ xs := by
  funext k
  by_cases hk : k = tm.k₁
  · subst k; simp [haltList, pointStack]
  · simp [haltList, pointStack, hk]

theorem representsEmpty_pointStack [DecidableEq K] [DecidableEq J]
    (e : StackEmbedding Γ Δ) (k : K) (xs : List (Γ k)) :
    e.RepresentsEmpty (pointStack k xs) (pointStack (e.index k) (xs.map (e.alphabet k))) := by
  refine ⟨e.represents_update e.represents_empty k xs, ?_⟩
  intro j hj
  simp [pointStack, Function.update_of_ne (hj k)]

theorem representsEmpty_pointStack_eq [DecidableEq K] [DecidableEq J]
    (e : StackEmbedding Γ Δ) (k : K) (xs : List (Γ k))
    (T : ∀ j, List (Δ j)) (h : e.RepresentsEmpty (pointStack k xs) T) :
    T = pointStack (e.index k) (xs.map (e.alphabet k)) :=
  e.representsEmpty_unique h (representsEmpty_pointStack e k xs)

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable (a b : FinTM2) (alphabet : a.Γ a.k₁ ≃ b.Γ b.k₀)

/-- First-phase simulation includes the exact continuation counter and empty
unused stacks. -/
def LeftRel (c : a.Cfg) (d : (sequentialMachine a b alphabet).Cfg) : Prop :=
  d.l = (c.l.map Sum.inl).or (some (Sum.inr b.main)) ∧
  d.var = (c.var, b.initialState) ∧
  (leftEmbedding a.k₁ b.k₀ alphabet).RepresentsEmpty c.stk d.stk

/-- Second-phase simulation includes the reset first control register and all
required empty first-bank stacks. -/
def RightRel (c : b.Cfg) (d : (sequentialMachine a b alphabet).Cfg) : Prop :=
  d.l = c.l.map Sum.inr ∧ d.var = (a.initialState, c.var) ∧
  (rightEmbedding a.k₁ a.Γ b.Γ).RepresentsEmpty c.stk d.stk

theorem sequential_left_step (c c' : a.Cfg) (d : (sequentialMachine a b alphabet).Cfg)
    (hc : a.step c = some c') (hr : LeftRel a b alphabet c d) :
    ∃ d', (sequentialMachine a b alphabet).step d = some d' ∧
      LeftRel a b alphabet c' d' := by
  rcases c with ⟨cl, cv, C⟩
  cases cl with
  | none => simp [FinTM2.step, step] at hc
  | some l =>
      simp only [FinTM2.step, step, Option.some.injEq] at hc
      subst c'
      rcases d with ⟨dl, dv, D⟩
      rcases hr with ⟨hl, hv, hs⟩
      change dl = some (Sum.inl l) at hl
      change dv = (cv, b.initialState) at hv
      subst dl; subst dv
      let e := leftEmbedding a.k₁ b.k₀ alphabet
      refine ⟨stepAux (redirectHalt (Sum.inr b.main) (liftStmt e Sum.inl (a.m l)))
        (cv, b.initialState) D, rfl, ?_⟩
      rw [redirectHalt_correct]
      obtain ⟨hh, ht⟩ := liftStmt_correct_empty e Sum.inl (a.m l) cv b.initialState C D hs
      exact ⟨congrArg (fun x => x.or (some (Sum.inr b.main))) hh.1, hh.2.1, ht⟩

theorem sequential_right_step (c c' : b.Cfg) (d : (sequentialMachine a b alphabet).Cfg)
    (hc : b.step c = some c') (hr : RightRel a b alphabet c d) :
    ∃ d', (sequentialMachine a b alphabet).step d = some d' ∧
      RightRel a b alphabet c' d' := by
  rcases c with ⟨cl, cv, C⟩
  cases cl with
  | none => simp [FinTM2.step, step] at hc
  | some l =>
      simp only [FinTM2.step, step, Option.some.injEq] at hc
      subst c'
      rcases d with ⟨dl, dv, D⟩
      rcases hr with ⟨hl, hv, hs⟩
      change dl = some (Sum.inr l) at hl
      change dv = (a.initialState, cv) at hv
      subst dl; subst dv
      let e := rightEmbedding a.k₁ a.Γ b.Γ
      refine ⟨stepAux (renameState (Equiv.prodComm b.σ a.σ) (liftStmt e Sum.inr (b.m l)))
        (a.initialState, cv) D, rfl, ?_⟩
      change RightRel a b alphabet _
        (stepAux (renameState (Equiv.prodComm b.σ a.σ) (liftStmt e Sum.inr (b.m l)))
          ((Equiv.prodComm b.σ a.σ) (cv, a.initialState)) D)
      rw [renameState_correct (Equiv.prodComm b.σ a.σ) (liftStmt e (Sum.inr : b.Λ → a.Λ ⊕ b.Λ) (b.m l)) (cv, a.initialState) D]
      obtain ⟨hh, ht⟩ := liftStmt_correct_empty e Sum.inr (b.m l) cv a.initialState C D hs
      refine ⟨hh.1, ?_, ht⟩
      exact congrArg Prod.swap hh.2.1

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable (a b : FinTM2) (alphabet : a.Γ a.k₁ ≃ b.Γ b.k₀)

/-- The external input obeys the original exact `initList` convention. -/
theorem sequential_initial (xs : List (a.Γ a.k₀)) :
    LeftRel a b alphabet (initList a xs)
      (initList (sequentialMachine a b alphabet)
        (xs.map ((leftEmbedding a.k₁ b.k₀ alphabet).alphabet a.k₀))) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [initList_stk, initList_stk]
  exact representsEmpty_pointStack (leftEmbedding a.k₁ b.k₀ alphabet) a.k₀ xs

/-- Finishing the first machine establishes the second machine's exact initial
store, including reset finite state and empty auxiliary stacks. -/
theorem sequential_handoff (ys : List (a.Γ a.k₁))
    (d : (sequentialMachine a b alphabet).Cfg)
    (h : LeftRel a b alphabet (haltList a ys) d) :
    RightRel a b alphabet (initList b (ys.map alphabet)) d := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hs := h.2.2
  rw [haltList_stk] at hs
  have he := representsEmpty_pointStack_eq (leftEmbedding a.k₁ b.k₀ alphabet) a.k₁ ys d.stk hs
  have he' : d.stk = pointStack (Γ := sharedAlphabet a.k₁ a.Γ b.Γ)
      (Sum.inr b.k₀) (ys.map alphabet) := by
    have hem : pointStack ((leftEmbedding a.k₁ b.k₀ alphabet).index a.k₁)
        (ys.map ((leftEmbedding a.k₁ b.k₀ alphabet).alphabet a.k₁)) =
        pointStack (Γ := sharedAlphabet a.k₁ a.Γ b.Γ) (Sum.inr b.k₀) (ys.map alphabet) := by
      have hi : (leftEmbedding a.k₁ b.k₀ alphabet).index a.k₁ = Sum.inr b.k₀ := by
        simp [leftEmbedding, leftIndex]
      have ha : HEq ((leftEmbedding a.k₁ b.k₀ alphabet).alphabet a.k₁) alphabet := by
        simp [leftEmbedding]
      have hgeneral : ∀ (j j' : SharedBank a.k₁ b.K)
          (e : a.Γ a.k₁ ≃ sharedAlphabet a.k₁ a.Γ b.Γ j)
          (e' : a.Γ a.k₁ ≃ sharedAlphabet a.k₁ a.Γ b.Γ j'),
          j = j' → HEq e e' → pointStack j (ys.map e) = pointStack j' (ys.map e') := by
        intro j j' e e' hj he
        subst j'
        cases he
        rfl
      exact hgeneral _ _ _ _ hi ha
    exact he.trans hem
  rw [he', initList_stk]
  simpa [rightEmbedding, Equiv.refl_apply] using
    representsEmpty_pointStack (rightEmbedding a.k₁ a.Γ b.Γ) b.k₀ (ys.map alphabet)

/-- The second terminal store is precisely the external `haltList`, with no
uncollected intermediate output or auxiliary garbage. -/
theorem sequential_final (zs : List (b.Γ b.k₁))
    (d : (sequentialMachine a b alphabet).Cfg)
    (h : RightRel a b alphabet (haltList b zs) d) :
    d = haltList (sequentialMachine a b alphabet) zs := by
  have hs := h.2.2
  rw [haltList_stk] at hs
  have he := representsEmpty_pointStack_eq (rightEmbedding a.k₁ a.Γ b.Γ) b.k₁ zs d.stk hs
  have he' : d.stk = pointStack (Γ := sharedAlphabet a.k₁ a.Γ b.Γ)
      (Sum.inr b.k₁) zs := by
    change d.stk = pointStack (Γ := sharedAlphabet a.k₁ a.Γ b.Γ)
      (Sum.inr b.k₁) (zs.map id) at he
    simpa only [List.map_id] using he
  have hl : d.l = none := h.1
  have hv : d.var = (a.initialState, b.initialState) := h.2.1
  rcases d with ⟨dl, dv, D⟩
  change dl = none at hl
  change dv = (a.initialState, b.initialState) at hv
  subst dl; subst dv
  congr 1
  exact he'.trans (haltList_stk (sequentialMachine a b alphabet) zs).symm

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

/-- Sequential composition has exactly the sum of the two machines' transition
counts. Sharing the intermediate stack needs no hidden copy or unit-cost word move. -/
def sequential_outputs (a b : FinTM2) (alphabet : a.Γ a.k₁ ≃ b.Γ b.k₀)
    (xs : List (a.Γ a.k₀)) (ys : List (a.Γ a.k₁)) (zs : List (b.Γ b.k₁))
    (n m : ℕ) (ha : TM2OutputsInTime a xs (some ys) n)
    (hb : TM2OutputsInTime b (ys.map alphabet) (some zs) m) :
    TM2OutputsInTime (sequentialMachine a b alphabet)
      (xs.map ((leftEmbedding a.k₁ b.k₀ alphabet).alphabet a.k₀)) (some zs) (m + n) where
  steps := hb.steps + ha.steps
  steps_le_m := Nat.add_le_add hb.steps_le_m ha.steps_le_m
  evals_in_steps := by
    let t := sequentialMachine a b alphabet
    let input := initList t (xs.map ((leftEmbedding a.k₁ b.k₀ alphabet).alphabet a.k₀))
    obtain ⟨d, hd, hr⟩ := simulate_iterations a.step t.step (LeftRel a b alphabet)
      (sequential_left_step a b alphabet) (initList a xs) (haltList a ys)
      input ha.steps ha.evals_in_steps (sequential_initial a b alphabet xs)
    obtain ⟨d', hd', hr'⟩ := simulate_iterations b.step t.step (RightRel a b alphabet)
      (sequential_right_step a b alphabet) (initList b (ys.map alphabet)) (haltList b zs)
      d hb.steps hb.evals_in_steps (sequential_handoff a b alphabet ys d hr)
    have he := sequential_final a b alphabet zs d' hr'
    subst d'
    change (fun x : Option t.Cfg => x.bind t.step)^[hb.steps + ha.steps] (some input) =
      some (haltList t zs)
    rw [Function.iterate_add_apply, hd]
    exact hd'

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Computability Polynomial

/-- Natural-coefficient time polynomials are monotone on natural input lengths. -/
theorem natPolynomial_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      intro x y hxy
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add (hp hxy) (hq hxy)
  | monomial n a =>
      intro x y hxy
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left hxy n)

/-- Actual sequential composition of polynomial-time TM2 computers, with a
proved machine compiler and an explicit composed time polynomial. This theorem
is independent of mathlib's unfinished similarly named declaration. -/
noncomputable def composeComputers {α β γ : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {ec : FinEncoding γ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime ea eb f) (h₂ : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) := by
  let alphabet := h₁.outputAlphabet.trans h₂.inputAlphabet.symm
  let e := leftEmbedding h₁.tm.k₁ h₂.tm.k₀ alphabet
  refine {
    tm := sequentialMachine h₁.tm h₂.tm alphabet
    inputAlphabet := (e.alphabet h₁.tm.k₀).symm.trans h₁.inputAlphabet
    outputAlphabet := h₂.outputAlphabet
    time := h₂.time.comp (outputLengthPolynomial h₁) + h₁.time
    outputsFun := ?_ }
  intro a
  have hm : ((eb.encode (f a)).map h₁.outputAlphabet.symm).map alphabet =
      (eb.encode (f a)).map h₂.inputAlphabet.symm := by
    simp [List.map_map, alphabet, Function.comp_def]
  have hb : TM2OutputsInTime h₂.tm
      (((eb.encode (f a)).map h₁.outputAlphabet.symm).map alphabet)
      (some ((ec.encode (g (f a))).map h₂.outputAlphabet.symm))
      (h₂.time.eval (eb.encode (f a)).length) :=
    { steps := (h₂.outputsFun (f a)).steps
      steps_le_m := (h₂.outputsFun (f a)).steps_le_m
      evals_in_steps := by
        rw [hm]
        exact (h₂.outputsFun (f a)).evals_in_steps }
  have hc := sequential_outputs h₁.tm h₂.tm alphabet
    ((ea.encode a).map h₁.inputAlphabet.symm)
    ((eb.encode (f a)).map h₁.outputAlphabet.symm)
    ((ec.encode (g (f a))).map h₂.outputAlphabet.symm)
    _ _ (h₁.outputsFun a) hb
  have hbound : h₂.time.eval (eb.encode (f a)).length + h₁.time.eval (ea.encode a).length ≤
      (h₂.time.comp (outputLengthPolynomial h₁) + h₁.time).eval (ea.encode a).length := by
    simp only [Polynomial.eval_add, Polynomial.eval_comp]
    exact Nat.add_le_add_right (natPolynomial_monotone h₂.time (encoded_output_length_le h₁ a)) _
  refine {
    steps := hc.steps
    steps_le_m := hc.steps_le_m.trans hbound
    evals_in_steps := ?_ }
  simpa only [List.map_map, Equiv.symm_trans_apply, Equiv.symm_symm,
    Function.comp_apply] using hc.evals_in_steps

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K J Λ Μ σ τ : Type} {Γ : K → Type} {Δ : J → Type}

@[simp] theorem pushBound_liftStmt (e : StackEmbedding Γ Δ) (labels : Λ → Μ)
    (q : Stmt Γ Λ σ) : pushBound (liftStmt (τ := τ) e labels q) = pushBound q := by
  induction q <;> simp_all [liftStmt, pushBound]

@[simp] theorem pushBound_renameState (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    pushBound (renameState e q) = pushBound q := by
  induction q <;> simp_all [renameState, pushBound]

@[simp] theorem pushBound_redirectHalt (next : Λ) (q : Stmt Γ Λ σ) :
    pushBound (redirectHalt next q) = pushBound q := by
  induction q <;> simp_all [redirectHalt, pushBound]

/-- If both input machines use finite alphabets on every stack, so does the
composed machine. No unbounded alphabet is introduced by the compiler. -/
def sequentialAlphabetFintype (a b : FinTM2) (alphabet : a.Γ a.k₁ ≃ b.Γ b.k₀)
    [∀ k, Fintype (a.Γ k)] [∀ k, Fintype (b.Γ k)] :
    ∀ k, Fintype ((sequentialMachine a b alphabet).Γ k)
  | .inl k => inferInstanceAs (Fintype (a.Γ k.val))
  | .inr k => inferInstanceAs (Fintype (b.Γ k))

end PlanarHom.MachineComposition

namespace PlanarHom.MachineComposition

open Turing Computability

/-- The compiler's recorded execution length is exactly additive, even after
transporting the external alphabet interfaces and polynomial bound. -/
@[simp] theorem composeComputers_steps {α β γ : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {ec : FinEncoding γ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime ea eb f) (h₂ : TM2ComputableInPolyTime eb ec g) (a : α) :
    ((composeComputers h₁ h₂).outputsFun a).steps =
      (h₂.outputsFun (f a)).steps + (h₁.outputsFun a).steps := rfl

end PlanarHom.MachineComposition
