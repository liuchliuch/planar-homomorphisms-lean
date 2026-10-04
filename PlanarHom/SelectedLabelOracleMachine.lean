import PlanarHom.MixedParallelCode
import PlanarHom.OracleSubstitution

/-! A genuine finite-control machine for the tagged counter/classifier oracle. -/

namespace PlanarHom.SelectedLabelOracleMachine
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.BinaryArithmetic PlanarHom.MachineComposition

inductive Label | dispatch | skipFirst | skipSecond | compare | success | failure | inc (l : Bool)
  deriving DecidableEq, Fintype

abbrev Statement := Stmt (fun _ : Bool=>Bool) Label (Option Bool)

def resetGoto (l : Label) : Statement := .load (fun _=>none) (.goto (fun _=>l))

def skipStmt (loop next : Label) : Statement :=
  .pop false (fun _ a=>a) (.branch (fun v=>v.getD false)
    (.pop false (fun _ a=>a) (resetGoto loop)) (resetGoto next))

/-- Compare against a fixed codeword by a finite, statically generated statement. -/
def compareStmt : Bits → Statement
  | [] => .pop false (fun _ a=>a) (.branch Option.isSome (resetGoto .failure) (resetGoto .success))
  | b::bs => .pop false (fun _ a=>a)
      (.branch (fun v=>v==some b) (compareStmt bs) (resetGoto .failure))

def compareRest : Bits → Bits → Bits
  | [], xs => xs.tail
  | _::_, [] => []
  | b::bs, a::xs => if a=b then compareRest bs xs else xs

/-- Pure label renaming recursively compiles actual statements. -/
def renameLabel {K Λ Μ σ : Type} {Γ : K→Type} (f : Λ→Μ) : Stmt Γ Λ σ → Stmt Γ Μ σ
  | .push k g q => .push k g (renameLabel f q)
  | .peek k g q => .peek k g (renameLabel f q)
  | .pop k g q => .pop k g (renameLabel f q)
  | .load g q => .load g (renameLabel f q)
  | .branch g q r => .branch g (renameLabel f q) (renameLabel f r)
  | .goto g => .goto (f∘g)
  | .halt => .halt

theorem renameLabel_correct {K Λ Μ σ : Type} {Γ : K→Type} [DecidableEq K]
    (f : Λ→Μ) (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k)) :
    stepAux (renameLabel f q) v S =
      ⟨(stepAux q v S).l.map f,(stepAux q v S).var,(stepAux q v S).stk⟩ := by
  induction q generalizing v S with
  | push k g q ih => exact ih _ _
  | peek k g q ih => exact ih _ _
  | pop k g q ih => exact ih _ _
  | load g q ih => exact ih _ _
  | branch g q r iq ir => cases h:g v <;> simp [renameLabel,stepAux,h,iq,ir]
  | goto => rfl
  | halt => rfl

def program (selected : ℕ) : Label → Statement
  | .dispatch => .pop false (fun _ a=>a) (.branch Option.isSome
      (.branch (fun v=>v.getD false) (resetGoto .skipFirst) (resetGoto (.inc false)))
      (.load (fun _=>none) .halt))
  | .skipFirst => skipStmt .skipFirst .skipSecond
  | .skipSecond => skipStmt .skipSecond .compare
  | .compare => compareStmt (BitEncoding.nat.encode selected)
  | .success => .push false (fun _=>true) (.load (fun _=>none) .halt)
  | .failure => .pop false (fun _ a=>a) (.branch Option.isSome (resetGoto .failure)
      (.push false (fun _=>false) (.load (fun _=>none) .halt)))
  | .inc l => renameLabel Label.inc (successorMachine.m l)

def machine (selected : ℕ) : FinTM2 where
  K := Bool
  Γ := fun _=>Bool
  k₀ := false
  k₁ := false
  Λ := Label
  main := .dispatch
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstance
  m := program selected

def store (xs ys : Bits) : Bool → Bits := fun k=>if k then ys else xs

def cfg (l : Option Label) (v : Option Bool) (xs ys : Bits) : Cfg (fun _ : Bool=>Bool) Label (Option Bool) :=
  ⟨l,v,store xs ys⟩

@[simp] theorem update_input (xs ys zs : Bits) : Function.update (store xs ys) false zs = store zs ys := by
  funext k; cases k <;> simp [store]
@[simp] theorem store_input (xs ys : Bits) : store xs ys false = xs := rfl

@[simp] theorem skip_nil (l next : Label) (v : Option Bool) :
    stepAux (skipStmt l next) v (store [] []) = cfg (some next) none [] [] := by
  simp [skipStmt,resetGoto,cfg,stepAux]

@[simp] theorem skip_false (l next : Label) (v : Option Bool) (xs : Bits) :
    stepAux (skipStmt l next) v (store (false::xs) []) = cfg (some next) none xs [] := by
  simp [skipStmt,resetGoto,cfg,stepAux]

@[simp] theorem skip_true (l next : Label) (v : Option Bool) (b : Bool) (xs : Bits) :
    stepAux (skipStmt l next) v (store (true::b::xs) []) = cfg (some l) none xs [] := by
  simp [skipStmt,resetGoto,cfg,stepAux]

@[simp] theorem skip_true_nil (l next : Label) (v : Option Bool) :
    stepAux (skipStmt l next) v (store [true] []) = cfg (some l) none [] [] := by
  simp [skipStmt,resetGoto,cfg,stepAux]

theorem skipFrame_length (xs : Bits) : (skipFrame xs).length ≤ xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [skipFrame]
  | singleton b => cases b <;> simp [skipFrame]
  | cons_cons a b xs ih _ => cases a <;> simp [skipFrame]; omega

/-- The parser's malformed-input behavior is proved for every raw bit string. -/
def skip_run (selected : ℕ) (l next : Label)
    (hp : program selected l = skipStmt l next) (xs : Bits) :
    EvalsToInTime (machine selected).step (cfg (some l) none xs [])
      (some (cfg (some next) none (skipFrame xs) [])) (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil =>
    apply oneStep
    simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux,skipFrame]
  | singleton b =>
    cases b with
    | false =>
      apply weakenTime (m:=2)
        (oneStep (machine selected).step (a:=cfg (some l) none [false] [])
          (b:=cfg (some next) none [] []) (by simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux]))
      decide
    | true =>
      have h₁ := oneStep (machine selected).step (a:=cfg (some l) none [true] [])
        (b:=cfg (some l) none [] []) (by simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux])
      have h₂ := oneStep (machine selected).step (a:=cfg (some l) none [] [])
        (b:=cfg (some next) none [] []) (by simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux])
      exact h₁.trans _ _ _ _ _ _ h₂
  | cons_cons a b xs ih _ =>
    cases a with
    | false =>
      apply weakenTime (oneStep (machine selected).step (a:=cfg (some l) none (false::b::xs) [])
        (b:=cfg (some next) none (b::xs) []) (by simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux]))
      simp
    | true =>
      have h₁ := oneStep (machine selected).step (a:=cfg (some l) none (true::b::xs) [])
        (b:=cfg (some l) none xs []) (by simp [machine,FinTM2.step,step,cfg,hp,skipStmt,resetGoto,stepAux])
      have hh := EvalsToInTime.trans (machine selected).step 1 (xs.length+1) _ _ _ h₁ ih
      exact weakenTime hh (by simp)


theorem compareRest_length (expected xs : Bits) : (compareRest expected xs).length ≤ xs.length := by
  induction expected generalizing xs with
  | nil => simp [compareRest]
  | cons b bs ih =>
    cases xs with
    | nil => simp [compareRest]
    | cons a xs =>
      by_cases h : a=b
      · simpa [compareRest,h] using (ih xs).trans (Nat.le_succ _)
      · simp [compareRest,h]

@[simp] theorem compareRest_self (xs : Bits) : compareRest xs xs = [] := by
  induction xs <;> simp_all [compareRest]

/-- The fixed-codeword comparison consumes only a prefix, preserves scratch,
and resets its register on both success and failure. -/
theorem compare_correct (expected xs : Bits) (v : Option Bool) :
    stepAux (compareStmt expected) v (store xs []) =
      cfg (some (if xs==expected then .success else .failure)) none (compareRest expected xs) [] := by
  induction expected generalizing xs v with
  | nil => cases xs <;> simp [compareStmt,compareRest,stepAux,resetGoto,cfg]
  | cons b bs ih =>
    cases xs with
    | nil => simp [compareStmt,compareRest,stepAux,resetGoto,cfg]
    | cons a xs =>
      by_cases h : a=b
      · subst a
        simpa [compareStmt,compareRest,stepAux,resetGoto,cfg] using ih xs (some b)
      · have hab : (a==b)=false := by cases a <;> cases b <;> simp_all
        simp [compareStmt,compareRest,stepAux,resetGoto,cfg,h,hab]

def failure_run (selected : ℕ) (xs : Bits) :
    EvalsToInTime (machine selected).step (cfg (some .failure) none xs [])
      (some (cfg none none [false] [])) (xs.length+1) := by
  induction xs with
  | nil =>
    apply oneStep
    simp [machine,FinTM2.step,step,program,stepAux,resetGoto,cfg]
  | cons b xs ih =>
    have hs := oneStep (machine selected).step (a:=cfg (some .failure) none (b::xs) [])
      (b:=cfg (some .failure) none xs []) (by simp [machine,FinTM2.step,step,program,stepAux,resetGoto,cfg])
    exact EvalsToInTime.trans (machine selected).step 1 (xs.length+1) _ _ _ hs ih

def compare_run (selected : ℕ) (xs : Bits) :
    EvalsToInTime (machine selected).step (cfg (some .compare) none xs [])
      (some (cfg none none [xs==BitEncoding.nat.encode selected] [])) (xs.length+2) := by
  have hs : (machine selected).step (cfg (some .compare) none xs []) =
      some (cfg (some (if xs==BitEncoding.nat.encode selected then .success else .failure)) none
        (compareRest (BitEncoding.nat.encode selected) xs) []) := by
    change some (stepAux (compareStmt _) none _) = _
    rw [compare_correct]
  by_cases he : xs=BitEncoding.nat.encode selected
  · subst xs
    simp only [BEq.rfl,compareRest_self] at hs ⊢
    have h₂ := oneStep (machine selected).step (a:=cfg (some .success) none [] [])
      (b:=cfg none none [true] []) (by simp [machine,FinTM2.step,step,program,stepAux,cfg])
    exact weakenTime (EvalsToInTime.trans (machine selected).step 1 1 _ _ _ (oneStep _ hs) h₂) (by omega)
  · have hne : (xs==BitEncoding.nat.encode selected)=false := by simp [he]
    rw [hne] at hs ⊢
    have h₂ := failure_run selected (compareRest (BitEncoding.nat.encode selected) xs)
    apply weakenTime (EvalsToInTime.trans (machine selected).step 1 _ _ _ _ (oneStep _ hs) h₂)
    have hlen := compareRest_length (BitEncoding.nat.encode selected) xs
    omega

def incCfg (c : successorMachine.Cfg) : Cfg (fun _ : Bool=>Bool) Label (Option Bool) :=
  ⟨c.l.map Label.inc,c.var,c.stk⟩

theorem inc_step (selected : ℕ) (c d : successorMachine.Cfg) (hs : successorMachine.step c = some d) :
    (machine selected).step (incCfg c) = some (incCfg d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at hs
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at hs
    subst d
    change some (stepAux (renameLabel Label.inc (successorMachine.m l)) v S) = _
    rw [renameLabel_correct]
    rfl

theorem inc_iter (selected : ℕ) (c d : successorMachine.Cfg) (n : ℕ)
    (hs : (fun c : Option successorMachine.Cfg=>c.bind successorMachine.step)^[n] (some c)=some d) :
    (fun c : Option (machine selected).Cfg=>c.bind (machine selected).step)^[n] (some (incCfg c))=
      some (incCfg d) := by
  obtain ⟨d',hh,he⟩ := simulate_iterations successorMachine.step (machine selected).step
    (fun c d=>d=incCfg c) (by intro c d e hs he; subst e; exact ⟨_,inc_step selected c d hs,rfl⟩)
    c d (incCfg c) n hs rfl
  simpa [he] using hh

def inc_run (selected : ℕ) (xs : Bits) :
    EvalsToInTime (machine selected).step (cfg (some (.inc false)) none xs [])
      (some (cfg none none (succBits xs) [])) (2*xs.length+2) where
  steps := (successor_outputs xs).steps
  steps_le_m := (successor_outputs xs).steps_le_m
  evals_in_steps := by
    have hh := inc_iter selected _ _ (successor_outputs xs).steps (successor_outputs xs).evals_in_steps
    have hi : incCfg (initList successorMachine xs) = cfg (some (.inc false)) none xs [] := by
      apply OracleSubstitution.cfg_ext
      · rfl
      · rfl
      · funext k; cases k <;> rfl
    have ho : incCfg (haltList successorMachine (succBits xs)) = cfg none none (succBits xs) [] := by
      apply OracleSubstitution.cfg_ext
      · rfl
      · rfl
      · funext k; cases k <;> rfl
    simpa [hi,ho] using hh


/-- Complete total raw-word behavior, including both dispatch tags and malformed
classification inputs. Each selected label determines one fixed finite program. -/
def tagged_run (selected : ℕ) (xs : Bits) :
    EvalsToInTime (machine selected).step (cfg (some .dispatch) none xs [])
      (some (cfg none none (selectedOracle selected xs) [])) (4*xs.length+6) := by
  cases xs with
  | nil =>
    apply weakenTime (oneStep (machine selected).step (a:=cfg (some .dispatch) none [] [])
      (b:=cfg none none [] []) (by simp [machine,FinTM2.step,step,program,stepAux,cfg]))
    decide
  | cons b xs =>
    cases b with
    | false =>
      have h₁ := oneStep (machine selected).step (a:=cfg (some .dispatch) none (false::xs) [])
        (b:=cfg (some (.inc false)) none xs [])
        (by simp [machine,FinTM2.step,step,program,stepAux,resetGoto,cfg])
      have h := EvalsToInTime.trans (machine selected).step 1 (2*xs.length+2) _ _ _ h₁ (inc_run selected xs)
      exact weakenTime h (by simp; omega)
    | true =>
      have h₁ := oneStep (machine selected).step (a:=cfg (some .dispatch) none (true::xs) [])
        (b:=cfg (some .skipFirst) none xs [])
        (by simp [machine,FinTM2.step,step,program,stepAux,resetGoto,cfg])
      have h₂ := skip_run selected .skipFirst .skipSecond rfl xs
      have h₃ := skip_run selected .skipSecond .compare rfl (skipFrame xs)
      have h₄ := compare_run selected (skipFrame (skipFrame xs))
      have h₁₂ := EvalsToInTime.trans (machine selected).step _ _ _ _ _ h₁ h₂
      have h₁₂₃ := EvalsToInTime.trans (machine selected).step _ _ _ _ _ h₁₂ h₃
      have h := EvalsToInTime.trans (machine selected).step _ _ _ _ _ h₁₂₃ h₄
      apply weakenTime h
      have ha := skipFrame_length xs
      have hb := skipFrame_length (skipFrame xs)
      simp only [List.length_cons]
      omega

theorem initial_eq (selected : ℕ) (xs : Bits) :
    initList (machine selected) xs = cfg (some .dispatch) none xs [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> rfl

theorem final_eq (selected : ℕ) (xs : Bits) :
    haltList (machine selected) xs = cfg none none xs [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> rfl

/-- A genuine polynomial-time computer for the selected-label oracle used by
the mixed-graph compiler; the oracle is never an assumed algorithmic interface. -/
noncomputable def computer (selected : ℕ) :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding BitEncoding.bits.toFinEncoding
      (selectedOracle selected) where
  tm := machine selected
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 4*Polynomial.X+Polynomial.C 6
  outputsFun xs := by
    simpa [TM2OutputsInTime,initial_eq,final_eq,BitEncoding.bits,BitEncoding.toFinEncoding,Equiv.refl]
      using tagged_run selected xs

theorem fp_selectedOracle (selected : ℕ) :
    FP BitEncoding.bits BitEncoding.bits (selectedOracle selected) := ⟨computer selected⟩

end PlanarHom.SelectedLabelOracleMachine
