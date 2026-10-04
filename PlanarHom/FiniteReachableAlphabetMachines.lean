import PlanarHom.Complexity
import Mathlib.Data.Set.Finite.Basic

/-! # Exact-time restriction of reachable stack alphabets to finite subtypes

Mathlib's bundled TM2 data allow arbitrary internal alphabet types. A finite
program with finite registers can nevertheless push only finitely many symbols.
This compiler retains those symbols and the complete finite input/output
alphabets. It changes neither control flow nor transition counts.
-/
namespace PlanarHom.FiniteReachableAlphabetMachines
open Turing Turing.TM2

section Syntax
variable {K Λ σ : Type} {Γ : K→Type}

/-- All possible pushed symbols, tagged by their stack, in finite syntax. -/
def pushSymbols : Stmt Γ Λ σ→Set (Sigma Γ)
  | .push k f q => Set.range (fun v => Sigma.mk k (f v)) ∪ pushSymbols q
  | .peek _ _ q => pushSymbols q
  | .pop _ _ q => pushSymbols q
  | .load _ q => pushSymbols q
  | .branch _ q r => pushSymbols q ∪ pushSymbols r
  | .goto _ => ∅
  | .halt => ∅

theorem pushSymbols_finite [Fintype σ] (q : Stmt Γ Λ σ) : (pushSymbols q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih => exact ih
  | pop k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ihq.union ihr
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- Per-stack restrictions are subtypes of the original symbols, not a new
unbounded data type or a free encoding operation. -/
def Alphabet (allowed : Set (Sigma Γ)) (k : K) := {a : Γ k // Sigma.mk k a ∈ allowed}

def compile (allowed : Set (Sigma Γ)) : (q : Stmt Γ Λ σ)→(pushSymbols q⊆allowed)→Stmt (Alphabet allowed) Λ σ
  | .push k f q,h => .push k (fun v => ⟨f v,h (Or.inl ⟨v,rfl⟩)⟩)
      (compile allowed q (fun _ ha => h (Or.inr ha)))
  | .peek k f q,h => .peek k (fun v a => f v (a.map Subtype.val)) (compile allowed q h)
  | .pop k f q,h => .pop k (fun v a => f v (a.map Subtype.val)) (compile allowed q h)
  | .load f q,h => .load f (compile allowed q h)
  | .branch f q r,h => .branch f (compile allowed q (fun _ ha => h (Or.inl ha)))
      (compile allowed r (fun _ ha => h (Or.inr ha)))
  | .goto f,_ => .goto f
  | .halt,_ => .halt

def eraseStore (allowed : Set (Sigma Γ)) (S : ∀k,List (Alphabet allowed k)) : ∀k,List (Γ k) :=
  fun k => (S k).map Subtype.val

def eraseCfg (allowed : Set (Sigma Γ)) (c : Cfg (Alphabet allowed) Λ σ) : Cfg Γ Λ σ :=
  ⟨c.l,c.var,eraseStore allowed c.stk⟩

theorem eraseStore_update [DecidableEq K] (allowed : Set (Sigma Γ))
    (S : ∀k,List (Alphabet allowed k)) (k : K) (xs : List (Alphabet allowed k)) :
    eraseStore allowed (Function.update S k xs)=Function.update (eraseStore allowed S) k (xs.map Subtype.val) := by
  funext j
  by_cases h : j=k
  · subst j; simp [eraseStore]
  · simp [eraseStore,Function.update_of_ne h]

/-- One restricted statement erases to exactly one original statement. -/
theorem compile_correct [DecidableEq K] (allowed : Set (Sigma Γ)) (q : Stmt Γ Λ σ)
    (h : pushSymbols q⊆allowed) (v : σ) (S : ∀k,List (Alphabet allowed k)) :
    eraseCfg allowed (stepAux (compile allowed q h) v S)=stepAux q v (eraseStore allowed S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [compile,stepAux,ih,eraseStore_update,List.map_cons]
    rfl
  | peek k f q ih =>
    simpa only [compile,stepAux,eraseStore,List.head?_map] using ih h (f v ((S k).head?.map Subtype.val)) S
  | pop k f q ih =>
    simp only [compile,stepAux,ih,eraseStore_update,List.map_tail,eraseStore,List.head?_map]
  | load f q ih => exact ih h (f v) S
  | branch f q r ihq ihr =>
    cases hv : f v <;> simp only [compile,stepAux,hv,Bool.cond_false,Bool.cond_true]
    · exact ihr _ v S
    · exact ihq _ v S
  | goto f => rfl
  | halt => rfl

theorem eraseCfg_injective (allowed : Set (Sigma Γ)) : Function.Injective (@eraseCfg K Λ σ Γ allowed) := by
  intro c d h
  cases c with
  | mk cl cv cs =>
    cases d with
    | mk dl dv ds =>
      have hl := congrArg Cfg.l h
      have hv := congrArg Cfg.var h
      dsimp only [eraseCfg] at hl hv
      subst dl; subst dv
      congr 1
      funext k
      have hs := congrArg (fun c => c.stk k) h
      exact List.map_injective_iff.mpr Subtype.val_injective hs

end Syntax

/-- Full input and output alphabets are retained to preserve both public
alphabet equivalences, together with every symbol that the finite program can push. -/
def allowedSymbols (tm : FinTM2) : Set (Sigma tm.Γ) :=
  (Set.range (fun a : tm.Γ tm.k₀ => Sigma.mk tm.k₀ a) ∪
    Set.range (fun a : tm.Γ tm.k₁ => Sigma.mk tm.k₁ a)) ∪ ⋃l,pushSymbols (tm.m l)

theorem allowedSymbols_finite (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] : (allowedSymbols tm).Finite := by
  letI := tm.Γk₀Fin
  letI := tm.ΛFin
  letI := tm.σFin
  exact ((Set.finite_range _).union (Set.finite_range _)).union
    (Set.finite_iUnion (fun l => pushSymbols_finite (tm.m l)))

theorem program_symbols_allowed (tm : FinTM2) (l : tm.Λ) : pushSymbols (tm.m l)⊆allowedSymbols tm := by
  intro a ha
  exact Or.inr (Set.mem_iUnion.mpr ⟨l,ha⟩)

noncomputable def alphabetFintypeOfMachine (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (k : tm.K) :
    Fintype (Alphabet (allowedSymbols tm) k) := by
  have hinj : Function.Injective (fun a : tm.Γ k => Sigma.mk k a) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact (Set.Finite.preimage (fun _ _ _ _ h => hinj h) (allowedSymbols_finite tm)).fintype

/-- Canonical subtype equivalence on the unchanged external input alphabet. -/
def inputEquiv (tm : FinTM2) : Alphabet (allowedSymbols tm) tm.k₀ ≃ tm.Γ tm.k₀ where
  toFun := Subtype.val
  invFun a := ⟨a,Or.inl (Or.inl ⟨a,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full output alphabet inclusion is essential for this equivalence, even for
symbols that happen not to occur in a particular terminating execution. -/
def outputEquiv (tm : FinTM2) : Alphabet (allowedSymbols tm) tm.k₁ ≃ tm.Γ tm.k₁ where
  toFun := Subtype.val
  invFun a := ⟨a,Or.inl (Or.inr ⟨a,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def machine (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] : FinTM2 := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI := alphabetFintypeOfMachine tm tm.k₀
  exact {
    K := tm.K
    k₀ := tm.k₀
    k₁ := tm.k₁
    Γ := Alphabet (allowedSymbols tm)
    Λ := tm.Λ
    main := tm.main
    σ := tm.σ
    initialState := tm.initialState
    m := fun l => compile (allowedSymbols tm) (tm.m l) (program_symbols_allowed tm l) }

private theorem cfg_ext {K Λ σ : Type} {Γ : K→Type} {c d : Cfg Γ Λ σ}
    (hl : c.l=d.l) (hv : c.var=d.var) (hs : c.stk=d.stk) : c=d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl

theorem erase_step (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (c : (machine tm).Cfg) :
    ((machine tm).step c).map (eraseCfg (allowedSymbols tm)) = tm.step (eraseCfg (allowedSymbols tm) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l =>
    change some (eraseCfg (allowedSymbols tm)
      (stepAux (compile (allowedSymbols tm) (tm.m l) (program_symbols_allowed tm l)) v S)) =
      some (stepAux (tm.m l) v (eraseStore (allowedSymbols tm) S))
    rw [compile_correct]

theorem simulate_step (tm : FinTM2) [Fintype (tm.Γ tm.k₁)]
    (a a' : tm.Cfg) (b : (machine tm).Cfg) (hs : tm.step a=some a')
    (hb : eraseCfg (allowedSymbols tm) b=a) :
    ∃b',(machine tm).step b=some b' ∧ eraseCfg (allowedSymbols tm) b'=a' := by
  have h := erase_step tm b
  rw [hb,hs] at h
  cases ht : (machine tm).step b with
  | none => rw [ht] at h; cases h
  | some b' => exact ⟨b',rfl,by simpa only [ht,Option.map_some,Option.some.injEq] using h⟩

theorem erase_initial (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (xs : List (tm.Γ tm.k₀)) :
    eraseCfg (allowedSymbols tm) (initList (machine tm) (xs.map (inputEquiv tm).symm))=initList tm xs := by
  apply cfg_ext
  · rfl
  · rfl
  change eraseStore (allowedSymbols tm) (initList (machine tm) (xs.map (inputEquiv tm).symm)).stk = _
  rw [MachineComposition.initList_stk,MachineComposition.initList_stk]
  simp only [MachineComposition.pointStack,eraseStore_update,List.map_map,inputEquiv,Equiv.coe_fn_symm_mk,
    Function.comp_def]
  change Function.update (fun k => ([] : List (tm.Γ k))) _ (List.map id _) = Function.update (fun k => ([] : List (tm.Γ k))) _ _
  rw [List.map_id]
  rfl

theorem erase_final (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (ys : List (tm.Γ tm.k₁)) :
    eraseCfg (allowedSymbols tm) (haltList (machine tm) (ys.map (outputEquiv tm).symm))=haltList tm ys := by
  apply cfg_ext
  · rfl
  · rfl
  change eraseStore (allowedSymbols tm) (haltList (machine tm) (ys.map (outputEquiv tm).symm)).stk = _
  rw [MachineComposition.haltList_stk,MachineComposition.haltList_stk]
  simp only [MachineComposition.pointStack,eraseStore_update,List.map_map,outputEquiv,Equiv.coe_fn_symm_mk,
    Function.comp_def]
  change Function.update (fun k => ([] : List (tm.Γ k))) _ (List.map id _) = Function.update (fun k => ([] : List (tm.Γ k))) _ _
  rw [List.map_id]
  rfl

/-- Every terminating source execution has a restricted execution with exactly
the same number of transitions and the exact strict halt-list configuration. -/
def outputs (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)) (n : ℕ)
    (h : TM2OutputsInTime tm xs (some ys) n) :
    TM2OutputsInTime (machine tm) (xs.map (inputEquiv tm).symm) (some (ys.map (outputEquiv tm).symm)) n := by
  refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
  obtain ⟨d,hd,he⟩ := MachineComposition.simulate_iterations tm.step (machine tm).step
    (fun a b => eraseCfg (allowedSymbols tm) b=a) (simulate_step tm)
    (initList tm xs) (haltList tm ys) (initList (machine tm) (xs.map (inputEquiv tm).symm)) h.steps
    h.evals_in_steps (erase_initial tm xs)
  have heq : d=haltList (machine tm) (ys.map (outputEquiv tm).symm) :=
    eraseCfg_injective (allowedSymbols tm) (he.trans (erase_final tm ys).symm)
  simpa only [heq] using hd

@[simp] theorem outputs_steps (tm : FinTM2) [Fintype (tm.Γ tm.k₁)] (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁))
    (n : ℕ) (h : TM2OutputsInTime tm xs (some ys) n) : (outputs tm xs ys n h).steps=h.steps := rfl

section Computers
open Complexity
variable {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β} {f : α→β}

noncomputable def sourceOutputFintype (h : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) :
    Fintype (h.tm.Γ h.tm.k₁) := Fintype.ofEquiv Bool h.outputAlphabet.symm

/-- Remove all inaccessible infinite-alphabet structure from an ordinary FP
witness. Inputs, outputs, control, registers, exact execution steps, and its
proved time polynomial remain unchanged. -/
noncomputable def restrictComputer (h : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) :
    TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f := by
  letI := sourceOutputFintype h
  exact {
    tm := machine h.tm
    inputAlphabet := (inputEquiv h.tm).trans h.inputAlphabet
    outputAlphabet := (outputEquiv h.tm).trans h.outputAlphabet
    time := h.time
    outputsFun := fun a => {
      steps := (h.outputsFun a).steps
      evals_in_steps := by
        have he := (outputs h.tm ((ea.encode a).map h.inputAlphabet.symm)
          ((eb.encode (f a)).map h.outputAlphabet.symm) _ (h.outputsFun a)).evals_in_steps
        simpa only [List.map_map] using he
      steps_le_m := (h.outputsFun a).steps_le_m } }

/-- Every stack of the restricted ordinary machine has an explicit finite alphabet. -/
noncomputable def alphabetFintype (h : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f)
    (k : (restrictComputer h).tm.K) : Fintype ((restrictComputer h).tm.Γ k) := by
  letI := sourceOutputFintype h
  exact alphabetFintypeOfMachine h.tm k

@[simp] theorem restrictComputer_time (h : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) :
    (restrictComputer h).time=h.time := rfl

@[simp] theorem restrictComputer_steps (h : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) (a : α) :
    ((restrictComputer h).outputsFun a).steps=(h.outputsFun a).steps := rfl

end Computers
end PlanarHom.FiniteReachableAlphabetMachines
