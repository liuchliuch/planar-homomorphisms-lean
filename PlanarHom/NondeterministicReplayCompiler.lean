import PlanarHom.NondeterministicTM2
import PlanarHom.StackTransfer
import PlanarHom.OracleSubstitution
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Literal deterministic replay of a binary nondeterministic TM2

Every source transition consumes a certificate bit. Deterministic transitions
require false; after halting all remaining bits must be false. The compiler
parses the actual framed paired input, simulates source instructions, and clears
all simulated stacks before returning its singleton Boolean answer.
-/
namespace PlanarHom.NondeterministicReplayCompiler
noncomputable section
open Turing Turing.TM2 Complexity MachineComposition NondeterministicTM2

inductive AuxStack | input | temp | result deriving DecidableEq, Fintype
inductive Phase | parse | restore | finish | pad | reject | done deriving DecidableEq, Fintype
abbrev Bank (m : Machine) := m.core.tm.K ⊕ AuxStack
def Alphabet (m : Machine) : Bank m → Type := Sum.elim m.core.tm.Γ (fun _ => Bool)
abbrev Label (m : Machine) := m.core.tm.Λ ⊕ (Phase ⊕ Finset m.core.tm.K)
abbrev State (m : Machine) := (m.core.tm.σ × Bool) × Option Bool

def source {m : Machine} (l : m.core.tm.Λ) : Label m := .inl l
def phase {m : Machine} (p : Phase) : Label m := .inr (.inl p)
def clear {m : Machine} (ks : Finset m.core.tm.K) : Label m := .inr (.inr ks)
def aux {m : Machine} (k : AuxStack) : Bank m := .inr k

def embedding (m : Machine) : StackEmbedding m.core.tm.Γ (Alphabet m) where
  index := ⟨Sum.inl, Sum.inl_injective⟩
  alphabet _ := Equiv.refl _

def control (m : Machine) : (m.core.tm.σ × (Bool × Option Bool)) ≃ State m :=
  (Equiv.prodAssoc _ _ _).symm

def lifted (m : Machine) (q : m.core.tm.Stmt) : Stmt (Alphabet m) (Label m) (State m) :=
  redirectHalt (phase .finish)
    (renameState (control m) (liftStmt (embedding m) source q))

def reset (m : Machine) (next : Label m) : Stmt (Alphabet m) (Label m) (State m) :=
  .load (fun v => (v.1,none)) (.goto (fun _ => next))

def program (m : Machine) : Label m → Stmt (Alphabet m) (Label m) (State m)
  | .inl l =>
      .pop (aux .input) (fun v b => (v.1,b))
        (.branch (fun v => v.2.isSome)
          (match m.branch l with
          | none => .branch (fun v => v.2.getD false)
              (reset m (phase .reject))
              (.load (fun v => (v.1,none)) (lifted m (m.core.tm.m l)))
          | some (l₀,l₁) => .branch (fun v => v.2.getD false)
              (reset m (source l₁)) (reset m (source l₀)))
          (reset m (phase .reject)))
  | .inr (.inl .parse) =>
      .pop (aux .input) (fun v b => (v.1,b))
        (.branch (fun v => v.2.getD false)
          (.pop (aux .input) (fun v b => (v.1,b))
            (.push (aux .temp) (fun v => v.2.getD false) (reset m (phase .parse))))
          (reset m (phase .restore)))
  | .inr (.inl .restore) =>
      transferStmt (aux .temp) (.inl m.core.tm.k₀) id m.core.inputAlphabet.symm
        (phase .restore) (source m.core.tm.main)
  | .inr (.inl .finish) =>
      .pop (.inl m.core.tm.k₁) (fun v b => ((v.1.1,b.map m.core.outputAlphabet == some true),none))
        (.peek (.inl m.core.tm.k₁) (fun v b => ((v.1.1,v.1.2 && b.isNone),none))
          (.goto (fun _ => phase .pad)))
  | .inr (.inl .pad) =>
      .pop (aux .input) (fun v b => (v.1,b))
        (.branch (fun v => v.2.isSome)
          (.load (fun v => ((v.1.1,v.1.2 && !v.2.getD false),none))
            (.goto (fun _ => phase .pad)))
          (.goto (fun _ => clear (@Finset.univ m.core.tm.K m.core.tm.kFin))))
  | .inr (.inl .reject) =>
      .load (fun v => ((v.1.1,false),none)) (.goto (fun _ => phase .pad))
  | .inr (.inl .done) =>
      .push (aux .result) (fun v => v.1.2)
        (.load (fun _ => ((m.core.tm.initialState,false),none)) .halt)
  | .inr (.inr ks) =>
      if h : ks.Nonempty then
        let k := h.choose
        clearStmt (.inl k) (clear ks) (clear (ks.erase k))
      else .goto (fun _ => phase .done)

def machine (m : Machine) : FinTM2 := by
  letI := m.core.tm.kFin
  letI := m.core.tm.ΛFin
  letI := m.core.tm.σFin
  exact {
    K := Bank m
    Γ := Alphabet m
    k₀ := aux .input
    k₁ := aux .result
    Λ := Label m
    main := phase .parse
    σ := State m
    initialState := ((m.core.tm.initialState,false),none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program m }

def store (m : Machine) (S : ∀k,List (m.core.tm.Γ k)) (xs tmp result : Bits) :
    ∀k,List (Alphabet m k)
  | .inl k => S k
  | .inr .input => xs
  | .inr .temp => tmp
  | .inr .result => result

def cfg (m : Machine) (l : Label m) (v : m.core.tm.σ) (b : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs tmp : Bits) : (machine m).Cfg :=
  ⟨some l,((v,b),none),store m S xs tmp []⟩

def active (m : Machine) (c : m.Cfg) (xs : Bits) : (machine m).Cfg :=
  ⟨(c.l.map source).or (some (phase .finish)),((c.var,false),none),store m c.stk xs [] []⟩

def iter (m : Machine) (n : ℕ) (c : (machine m).Cfg) :=
  (fun c : Option (machine m).Cfg => c.bind (machine m).step)^[n] (some c)

theorem iter_trans (m : Machine) {a b c : (machine m).Cfg} {n k : ℕ}
    (h : iter m n a = some b) (h' : iter m k b = some c) :
    iter m (n+k) a = some c := by
  rw [Nat.add_comm,iter,Function.iterate_add_apply]
  change (fun c : Option (machine m).Cfg => c.bind (machine m).step)^[k] (iter m n a) = _
  rw [h]
  exact h'


theorem lifted_correct (m : Machine) (q : m.core.tm.Stmt) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) :
    stepAux (lifted m q) ((v,false),none) (store m S xs [] []) =
      active m (stepAux q v S) xs := by
  let e := embedding m
  have hs : e.Represents S (store m S xs [] []) := by
    intro k
    change S k = (S k).map id
    simp
  have h := liftStmt_correct e (source (m:=m)) q v (false,(none : Option Bool)) S
    (store m S xs [] []) hs
  unfold lifted
  rw [redirectHalt_correct]
  change continueCfg _ (stepAux (renameState (control m) (liftStmt e source q))
    ((control m) (v,(false,none))) _) = _
  rw [renameState_correct]
  apply OracleSubstitution.cfg_ext
  · exact congrArg (fun l => l.or (some (phase .finish))) h.1
  · exact congrArg (control m) h.2.1
  · funext k
    cases k with
    | inl k =>
      have hh := h.2.2 k
      change _ = List.map id _ at hh
      simpa only [List.map_id] using hh
    | inr k =>
      have he := liftStmt_untouched e source q (v,(false,(none : Option Bool)))
        (store m S xs [] []) (.inr k) (by intro j; simp [e,embedding])
      cases k <;> exact he

theorem store_update_input (m : Machine) (S : ∀k,List (m.core.tm.Γ k))
    (xs ys tmp result : Bits) :
    Function.update (store m S xs tmp result) (aux .input) ys = store m S ys tmp result := by
  funext k
  cases k with
  | inl k => simp [store,aux]
  | inr k => cases k <;> simp [store,aux]

theorem ordinary_step (m : Machine) (l : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) (h : m.branch l = none) :
    (machine m).step (active m ⟨some l,v,S⟩ (false::xs)) =
      some (active m (stepAux (m.core.tm.m l) v S) xs) := by
  change some (stepAux (program m (source l)) ((v,false),none)
    (store m S (false::xs) [] [])) = _
  simp only [program,source,stepAux,store,aux,h,Option.isSome_some,Bool.cond_true,
    Option.getD_some,Bool.cond_false,List.head?_cons,List.tail_cons]
  rw [show Function.update (store m S (false::xs) [] []) (.inr AuxStack.input) xs =
    store m S xs [] [] from store_update_input m S _ _ _ _]
  rw [lifted_correct]

theorem branch_step (m : Machine) (l l₀ l₁ : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (b : Bool) (xs : Bits)
    (h : m.branch l = some (l₀,l₁)) :
    (machine m).step (active m ⟨some l,v,S⟩ (b::xs)) =
      some (active m ⟨some (if b then l₁ else l₀),v,S⟩ xs) := by
  cases b <;>
    simp [FinTM2.step,Turing.TM2.step,active,machine,program,source,stepAux,store,aux,h,
      reset] <;> exact store_update_input m S _ _ _ _


theorem store_update_source (m : Machine) (S : ∀k,List (m.core.tm.Γ k))
    (j : m.core.tm.K) (ys : List (m.core.tm.Γ j)) (xs tmp result : Bits) :
    Function.update (store m S xs tmp result) (.inl j) ys =
      store m (Function.update S j ys) xs tmp result := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k=j
    · subst k; simp [store]
    · simp [store,Function.update_of_ne h,Function.update_of_ne (show Sum.inl k ≠ (Sum.inl j : Bank m) by simpa)]
  | inr k => cases k <;> simp [store]

def final (m : Machine) (b : Bool) : (machine m).Cfg := haltList (machine m) [b]

theorem done_step (m : Machine) (v : m.core.tm.σ) (b : Bool) :
    (machine m).step (cfg m (phase .done) v b (fun _ => []) [] []) = some (final m b) := by
  change some (stepAux (program m (phase .done)) _ _) = _
  congr 1
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => simp [stepAux,program,phase,aux,store,final,haltList,machine]
    | inr k => cases k <;> simp [stepAux,program,phase,aux,store,final,haltList,machine]

theorem clear_run_bound (m : Machine) (ks : Finset m.core.tm.K)
    (v : m.core.tm.σ) (b : Bool) (S : ∀k,List (m.core.tm.Γ k)) (n : ℕ)
    (hlen : ∀k,(S k).length ≤ n) (hout : ∀k,k∉ks → S k=[]) :
    ∃ t, t ≤ ks.card*(n+1)+2 ∧
      iter m t (cfg m (clear ks) v b S [] []) = some (final m b) := by
  classical
  induction ks using Finset.strongInductionOn generalizing S with
  | _ ks ih =>
    by_cases hks : ks.Nonempty
    · let k := hks.choose
      have hk : k∈ks := hks.choose_spec
      let S' := Function.update S k []
      have hl' : ∀j,(S' j).length ≤ n := by
        intro j; by_cases h : j=k
        · subst j; simp [S']
        · simpa [S',Function.update_of_ne h] using hlen j
      have ho' : ∀j,j∉ks.erase k → S' j=[] := by
        intro j hj
        by_cases h : j=k
        · subst j; simp [S']
        · simpa [S',Function.update_of_ne h] using hout j (by simpa [h] using hj)
      obtain ⟨t,ht,hr⟩ := ih (ks.erase k) (Finset.erase_ssubset hk) S' hl' ho'
      have hprog : program m (clear ks) =
          clearStmt (.inl k) (clear ks) (clear (ks.erase k)) := by
        simp [program,clear,hks,k]
      have hc := MachineComposition.clear_run (program m) (.inl k)
        (clear ks) (clear (ks.erase k)) hprog (v,b) none (store m S [] [] [])
      have hrun : iter m ((S k).length+1) (cfg m (clear ks) v b S [] []) =
          some (cfg m (clear (ks.erase k)) v b S' [] []) := by
        simpa only [iter,cfg,store,FinTM2.step,machine,store_update_source,S'] using hc
      refine ⟨(S k).length+1+t,?_,iter_trans m hrun hr⟩
      have hcard := Finset.card_erase_add_one hk
      have hn := hlen k
      nlinarith
    · have he : ks=∅ := Finset.not_nonempty_iff_eq_empty.mp hks
      subst ks
      have hs : S = fun _ => [] := funext (fun k => hout k (by simp))
      subst S
      refine ⟨2,by simp,?_⟩
      have hc : (machine m).step (cfg m (clear ∅) v b (fun _=>[]) [] []) =
          some (cfg m (phase .done) v b (fun _=>[]) [] []) := by
        simp [FinTM2.step,Turing.TM2.step,cfg,machine,program,clear]
      simpa [iter,Function.iterate_succ_apply,hc,done_step] using
        (done_step m v b)


theorem pad_step_cons (m : Machine) (v : m.core.tm.σ) (b a : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) :
    (machine m).step (cfg m (phase .pad) v b S (a::xs) []) =
      some (cfg m (phase .pad) v (b && !a) S xs []) := by
  change some (stepAux (program m (phase .pad)) _ _) = _
  simp only [program,phase,stepAux,cfg,store,aux,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some]
  congr 1
  exact OracleSubstitution.cfg_ext rfl rfl (store_update_input m S _ _ _ _)

theorem pad_run (m : Machine) (v : m.core.tm.σ) (b : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) :
    iter m (xs.length+1) (cfg m (phase .pad) v b S xs []) =
      some (cfg m (clear (@Finset.univ m.core.tm.K m.core.tm.kFin))
        v (b && xs.all (! ·)) S [] []) := by
  induction xs generalizing b with
  | nil =>
    change (machine m).step (cfg m (phase .pad) v b S [] []) = _
    simp only [FinTM2.step,Turing.TM2.step,cfg,machine,phase,program,stepAux,aux,store,
      List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,List.all_nil,Bool.and_true]
    congr 1
    exact OracleSubstitution.cfg_ext rfl rfl (store_update_input m S [] [] [] [])
  | cons a xs ih =>
    rw [List.length_cons,Nat.add_assoc,iter,Function.iterate_succ_apply]
    change (fun c : Option (machine m).Cfg => c.bind (machine m).step)^[xs.length+1]
      ((machine m).step (cfg m (phase .pad) v b S (a::xs) [])) = _
    rw [pad_step_cons]
    simpa [iter,Bool.and_assoc] using ih (b && !a)

theorem finish_step (m : Machine) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) :
    (machine m).step (active m ⟨none,v,S⟩ xs) =
      some (cfg m (phase .pad) v (decide ((S m.core.tm.k₁).map m.core.outputAlphabet=[true]))
        (Function.update S m.core.tm.k₁ (S m.core.tm.k₁).tail) xs []) := by
  have hbool : (((S m.core.tm.k₁).head?.map m.core.outputAlphabet == some true) &&
      (S m.core.tm.k₁).tail.head?.isNone) =
        decide ((S m.core.tm.k₁).map m.core.outputAlphabet=[true]) := by
    cases h : S m.core.tm.k₁ with
    | nil => simp
    | cons a as =>
      cases as with
      | nil => cases ha : m.core.outputAlphabet a <;> simp [ha]
      | cons d ds => simp
  change some (stepAux (program m (phase .finish)) ((v,false),none)
    (store m S xs [] [])) = _
  simp only [program,phase,stepAux,store,Function.update_self]
  rw [hbool,store_update_source]
  rfl


def stackCount (m : Machine) : ℕ := @Fintype.card m.core.tm.K m.core.tm.kFin

theorem pad_outputs (m : Machine) (v : m.core.tm.σ) (b : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) (n : ℕ) (hlen : ∀k,(S k).length ≤ n) :
    ∃ t, t ≤ xs.length + stackCount m*(n+1)+3 ∧
      iter m t (cfg m (phase .pad) v b S xs []) = some (final m (b && xs.all (! ·))) := by
  classical
  letI := m.core.tm.kFin
  obtain ⟨t,ht,hr⟩ := clear_run_bound m Finset.univ v (b && xs.all (! ·)) S n hlen (by simp)
  refine ⟨xs.length+1+t,?_,iter_trans m (pad_run m v b S xs) hr⟩
  simp only [Finset.card_univ] at ht
  dsimp only [stackCount]
  omega

theorem tail_length_bound (m : Machine) (S : ∀k,List (m.core.tm.Γ k))
    (j : m.core.tm.K) (n : ℕ) (hlen : ∀k,(S k).length ≤ n) :
    ∀k,((Function.update S j (S j).tail) k).length ≤ n := by
  intro k
  by_cases h : k=j
  · subst k; simp only [Function.update_self,List.length_tail]; have := hlen j; omega
  · simpa [Function.update_of_ne h] using hlen k

theorem halted_outputs (m : Machine) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) (n : ℕ) (hlen : ∀k,(S k).length ≤ n) :
    ∃ t, t ≤ xs.length + stackCount m*(n+1)+4 ∧
      iter m t (active m ⟨none,v,S⟩ xs) =
        some (final m (NondeterministicComputationTree.replay m.view ⟨none,v,S⟩ xs)) := by
  obtain ⟨t,ht,hr⟩ := pad_outputs m v
    (decide ((S m.core.tm.k₁).map m.core.outputAlphabet=[true]))
    (Function.update S m.core.tm.k₁ (S m.core.tm.k₁).tail) xs n (tail_length_bound m S _ n hlen)
  have he : (decide ((S m.core.tm.k₁).map m.core.outputAlphabet=[true]) && xs.all (! ·)) =
      NondeterministicComputationTree.replay m.view ⟨none,v,S⟩ xs := by
    by_cases h : (S m.core.tm.k₁).map m.core.outputAlphabet=[true]
    · simp [h,NondeterministicComputationTree.replay_accept m.view
        (show m.view ⟨none,v,S⟩ = .accept by simp [Machine.view,Machine.output,h])]
    · simp [h,NondeterministicComputationTree.replay_reject m.view
        (show m.view ⟨none,v,S⟩ = .reject by simp [Machine.view,Machine.output,h])]
  refine ⟨1+t,by omega,?_⟩
  rw [← he]
  exact iter_trans m (show iter m 1 _ = _ from finish_step m v S xs) hr

theorem reject_step (m : Machine) (v : m.core.tm.σ) (b : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) :
    (machine m).step (cfg m (phase .reject) v b S xs []) =
      some (cfg m (phase .pad) v false S xs []) := rfl

theorem reject_outputs (m : Machine) (v : m.core.tm.σ) (b : Bool)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) (n : ℕ) (hlen : ∀k,(S k).length ≤ n) :
    ∃ t, t ≤ xs.length + stackCount m*(n+1)+4 ∧
      iter m t (cfg m (phase .reject) v b S xs []) = some (final m false) := by
  obtain ⟨t,ht,hr⟩ := pad_outputs m v false S xs n hlen
  refine ⟨1+t,by omega,?_⟩
  simpa only [Bool.false_and] using iter_trans m
    (show iter m 1 (cfg m (phase .reject) v b S xs []) = _ from reject_step m v b S xs) hr

theorem active_nil_step (m : Machine) (l : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) :
    (machine m).step (active m ⟨some l,v,S⟩ []) =
      some (cfg m (phase .reject) v false S [] []) := by
  change some (stepAux (program m (source l)) _ _) = _
  simp only [program,source,stepAux,store,aux,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,reset]
  congr 1
  exact OracleSubstitution.cfg_ext rfl rfl (store_update_input m S [] [] [] [])

theorem invalid_bit_step (m : Machine) (l : m.core.tm.Λ) (v : m.core.tm.σ)
    (S : ∀k,List (m.core.tm.Γ k)) (xs : Bits) (h : m.branch l=none) :
    (machine m).step (active m ⟨some l,v,S⟩ (true::xs)) =
      some (cfg m (phase .reject) v false S xs []) := by
  change some (stepAux (program m (source l)) _ _) = _
  simp only [program,source,stepAux,store,aux,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some,h,reset]
  congr 1
  exact OracleSubstitution.cfg_ext rfl rfl (store_update_input m S _ _ _ _)

def runBound (m : Machine) (n w : ℕ) : ℕ :=
  stackCount m*(n+1)+(stackCount m*machinePushBound m.core.tm+3)*w+5

theorem active_outputs (m : Machine) (c : m.Cfg) (xs : Bits) (n : ℕ)
    (hlen : ∀k,(c.stk k).length ≤ n) :
    ∃ t, t ≤ runBound m n xs.length ∧ iter m t (active m c xs) =
      some (final m (NondeterministicComputationTree.replay m.view c xs)) := by
  induction xs generalizing c n with
  | nil =>
    rcases c with ⟨l,v,S⟩
    cases l with
    | none =>
      obtain ⟨t,ht,hr⟩ := halted_outputs m v S [] n hlen
      exact ⟨t,by simpa [runBound] using ht.trans (by simp),hr⟩
    | some l =>
      obtain ⟨t,ht,hr⟩ := reject_outputs m v false S [] n hlen
      refine ⟨1+t,by simp [runBound] at *; omega,?_⟩
      have hx : NondeterministicComputationTree.replay m.view ⟨some l,v,S⟩ [] = false := by
        cases h : m.branch l <;> simp [NondeterministicComputationTree.replay,Machine.view,h]
      rw [hx]
      exact iter_trans m (show iter m 1 _ = _ from active_nil_step m l v S) hr
  | cons a xs ih =>
    rcases c with ⟨l,v,S⟩
    cases l with
    | none =>
      obtain ⟨t,ht,hr⟩ := halted_outputs m v S (a::xs) n hlen
      refine ⟨t,ht.trans ?_,hr⟩
      simp only [runBound,List.length_cons,Nat.add_mul,Nat.mul_add]
      omega
    | some l =>
      cases hb : m.branch l with
      | none =>
        cases a with
        | true =>
          obtain ⟨t,ht,hr⟩ := reject_outputs m v false S xs n hlen
          refine ⟨1+t,?_,?_⟩
          · simp only [runBound,List.length_cons,Nat.add_mul,Nat.mul_add] at *; omega
          · have hx : NondeterministicComputationTree.replay m.view ⟨some l,v,S⟩ (true::xs) = false := by
              simp [NondeterministicComputationTree.replay,Machine.view,hb]
            rw [hx]
            exact iter_trans m (show iter m 1 _ = _ from invalid_bit_step m l v S xs hb) hr
        | false =>
          let d := stepAux (m.core.tm.m l) v S
          have hd : m.core.tm.step ⟨some l,v,S⟩ = some d := rfl
          have hn := step_length_le m.core.tm hd n hlen
          obtain ⟨t,ht,hr⟩ := ih d (n+machinePushBound m.core.tm) hn
          refine ⟨1+t,?_,?_⟩
          · simp only [runBound,List.length_cons,Nat.add_mul,Nat.mul_add] at *; omega
          · have hx : NondeterministicComputationTree.replay m.view ⟨some l,v,S⟩ (false::xs) =
                NondeterministicComputationTree.replay m.view d xs := by
              simp [NondeterministicComputationTree.replay,Machine.view,hb,d]
            rw [hx]
            exact iter_trans m (show iter m 1 _ = _ from ordinary_step m l v S xs hb) hr
      | some ls =>
        rcases ls with ⟨l₀,l₁⟩
        obtain ⟨t,ht,hr⟩ := ih ⟨some (if a then l₁ else l₀),v,S⟩ n hlen
        refine ⟨1+t,?_,?_⟩
        · simp only [runBound,List.length_cons,Nat.add_mul,Nat.mul_add] at *; omega
        · have hx : NondeterministicComputationTree.replay m.view ⟨some l,v,S⟩ (a::xs) =
              NondeterministicComputationTree.replay m.view ⟨some (if a then l₁ else l₀),v,S⟩ xs := by
            cases a <;> simp [NondeterministicComputationTree.replay,Machine.view,Machine.jump,hb]
          rw [hx]
          exact iter_trans m (show iter m 1 _ = _ from branch_step m l l₀ l₁ v S a xs hb) hr


theorem store_update_temp (m : Machine) (S : ∀k,List (m.core.tm.Γ k))
    (xs tmp ys result : Bits) :
    Function.update (store m S xs tmp result) (aux .temp) ys = store m S xs ys result := by
  funext k
  cases k with
  | inl k => simp [store,aux]
  | inr k => cases k <;> simp [store,aux]

theorem parse_step_cons (m : Machine) (v : m.core.tm.σ) (S : ∀k,List (m.core.tm.Γ k))
    (a : Bool) (xs ys tmp : Bits) :
    (machine m).step (cfg m (phase .parse) v false S
      (BitEncoding.frame (a::xs) ++ ys) tmp) =
      some (cfg m (phase .parse) v false S (BitEncoding.frame xs ++ ys) (a::tmp)) := by
  change some (stepAux (program m (phase .parse)) _ _) = _
  simp only [program,phase,stepAux,cfg,BitEncoding.frame,List.cons_append,store,aux,
    List.head?_cons,List.tail_cons,Option.getD_some,Bool.cond_true,reset,Function.update_self,
    Function.update_idem,Function.update_of_ne (show (Sum.inr AuxStack.temp : Bank m) ≠ .inr AuxStack.input by intro h; cases h)]
  congr 1
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  rw [show Function.update (store m S (true::a::(BitEncoding.frame xs++ys)) tmp []) (.inr AuxStack.input)
      (BitEncoding.frame xs++ys) = store m S (BitEncoding.frame xs++ys) tmp [] from
        store_update_input m S _ _ _ _]
  exact store_update_temp m S _ _ _ _

theorem parse_step_nil (m : Machine) (v : m.core.tm.σ) (S : ∀k,List (m.core.tm.Γ k))
    (ys tmp : Bits) :
    (machine m).step (cfg m (phase .parse) v false S (BitEncoding.frame [] ++ ys) tmp) =
      some (cfg m (phase .restore) v false S ys tmp) := by
  change some (stepAux (program m (phase .parse)) _ _) = _
  simp only [program,phase,stepAux,cfg,BitEncoding.frame,List.cons_append,List.nil_append,store,aux,
    List.head?_cons,List.tail_cons,Option.getD_some,Bool.cond_false,reset]
  congr 1
  exact OracleSubstitution.cfg_ext rfl rfl (store_update_input m S _ _ _ _)

theorem parse_run (m : Machine) (v : m.core.tm.σ) (S : ∀k,List (m.core.tm.Γ k))
    (xs ys tmp : Bits) :
    iter m (xs.length+1) (cfg m (phase .parse) v false S (BitEncoding.frame xs++ys) tmp) =
      some (cfg m (phase .restore) v false S ys (xs.reverse++tmp)) := by
  induction xs generalizing tmp with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      parse_step_nil m v S ys tmp
  | cons a xs ih =>
    rw [List.length_cons,Nat.add_assoc,iter,Function.iterate_succ_apply]
    change (fun c : Option (machine m).Cfg => c.bind (machine m).step)^[xs.length+1]
      ((machine m).step (cfg m (phase .parse) v false S (BitEncoding.frame (a::xs)++ys) tmp)) = _
    rw [parse_step_cons]
    simpa [iter,List.reverse_cons,List.append_assoc] using ih (a::tmp)

theorem restore_run (m : Machine) (xs ys : Bits) :
    iter m (xs.length+1)
      (cfg m (phase .restore) m.core.tm.initialState false (fun _=>[]) ys xs.reverse) =
      some (active m (m.initial xs) ys) := by
  have h := transfer_run (program m) (aux .temp) (.inl m.core.tm.k₀)
    (by intro he; cases he) id m.core.inputAlphabet.symm (phase .restore) (source m.core.tm.main)
    rfl (m.core.tm.initialState,false) none (store m (fun _=>[]) ys xs.reverse [])
  have hs : transferStore (aux .temp) (.inl m.core.tm.k₀) (m.core.inputAlphabet.symm ∘ id)
      (store m (fun _=>[]) ys xs.reverse []) = store m (m.initial xs).stk ys [] [] := by
    funext k
    cases k with
    | inl k =>
      by_cases hk : k=m.core.tm.k₀
      · subst k
        simp [transferStore,store,aux,Machine.initial,initList,List.map_reverse]
      · simp [transferStore,store,aux,Machine.initial,initList,hk]
    | inr k => cases k <;> simp [transferStore,store,aux]
  rw [hs] at h
  simpa only [iter,FinTM2.step,machine,cfg,active,Machine.initial,initList,aux,store,
    List.length_reverse,Option.map_some,Option.or_some] using h

theorem initial_eq (m : Machine) (xs ys : Bits) :
    initList (machine m) (BitEncoding.frame xs++ys) =
      cfg m (phase .parse) m.core.tm.initialState false (fun _=>[])
        (BitEncoding.frame xs++ys) [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k => simp [initList,machine,aux,cfg,store]
  | inr k => cases k <;> simp [initList,machine,aux,cfg,store]

theorem initial_stack_bound (m : Machine) (xs : Bits) :
    ∀k,((m.initial xs).stk k).length ≤ xs.length := by
  intro k
  by_cases hk : k=m.core.tm.k₀
  · subst k; simp [Machine.initial,initList]
  · simp [Machine.initial,initList,hk]

def verifier (m : Machine) (x : Bits × Bits) : Bool :=
  NondeterministicComputationTree.replay m.view (m.initial x.1) x.2

def time (m : Machine) : Polynomial ℕ :=
  Polynomial.C (stackCount m+stackCount m*machinePushBound m.core.tm+5)*Polynomial.X+
    Polynomial.C (stackCount m+7)

theorem outputs (m : Machine) (xs ys : Bits) :
    ∃ t, t ≤ (time m).eval (BitEncoding.frame xs++ys).length ∧
      iter m t (initList (machine m) (BitEncoding.frame xs++ys)) = some (final m (verifier m (xs,ys))) := by
  have hp := parse_run m m.core.tm.initialState (fun _=>[]) xs ys []
  simp only [List.append_nil] at hp
  have hi := iter_trans m hp (restore_run m xs ys)
  rw [← initial_eq] at hi
  obtain ⟨t,ht,hr⟩ := active_outputs m (m.initial xs) ys xs.length (initial_stack_bound m xs)
  refine ⟨(xs.length+1)+(xs.length+1)+t,?_,iter_trans m hi hr⟩
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    List.length_append,BitEncoding.frame_length,runBound] at ht ⊢
  ring_nf at ht ⊢
  omega

/-- This is an actual linear-time deterministic TM2 verifier of any bounded
nondeterministic replay, including rejecting truncated or noncanonical choices. -/
def computer (m : Machine) : TM2ComputableInPolyTime
    (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding BitEncoding.bool.toFinEncoding (verifier m) where
  tm := machine m
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time m
  outputsFun x := Classical.choice (by
    obtain ⟨t,ht,hr⟩ := outputs m x.1 x.2
    exact ⟨{ steps := t
             evals_in_steps := by simpa [BitEncoding.toFinEncoding,BitEncoding.prod,BitEncoding.bits,
               BitEncoding.bool,Equiv.refl,iter,final] using hr
             steps_le_m := ht }⟩)

theorem fp_verifier (m : Machine) :
    FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool (verifier m) := ⟨computer m⟩

end
end PlanarHom.NondeterministicReplayCompiler
