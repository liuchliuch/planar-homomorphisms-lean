import PlanarHom.OracleSubstitution
import PlanarHom.OracleRunAccounting
import PlanarHom.RelationalStackTransfer

/-!
# Composition of actual oracle reductions

The ordinary call protocol is reused, but callee query labels remain real oracle
instructions. Complete nested transcripts and their promise validity are retained.
-/

namespace PlanarHom.OracleReductionComposition

noncomputable section

open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition
open PlanarHom.OracleSubstitution

/-- Only the callee bank can issue an external oracle query. Caller requests are
implemented by the already-verified finite-control subroutine protocol. -/
def composeMachine (m g : OracleTM2) : OracleTM2 where
  core := {
    tm := OracleSubstitution.machine m g.core
    inputAlphabet := m.core.inputAlphabet
    outputAlphabet := m.core.outputAlphabet }
  finiteAlphabet := @OracleSubstitution.alphabetFintype m g.core g.finiteAlphabet
  queryStack := .inr (.inl g.queryStack)
  answerStack := .inr (.inl g.answerStack)
  queryAlphabet := g.queryAlphabet
  answerAlphabet := g.answerAlphabet
  request
    | .inr (.inr (next,l)) => (g.request l).map (callee next)
    | _ => none

variable (m g : OracleTM2) (oracle : Bits → Bits)

abbrev Pure (c d : (composeMachine m g).Cfg) (n : ℕ) : Prop :=
  (composeMachine m g).Run oracle c d n n []

theorem pure_trans {c d e : (composeMachine m g).Cfg} {n t : ℕ}
    (h : Pure m g oracle c d n) (h' : Pure m g oracle d e t) :
    Pure m g oracle c e (n+t) := by
  simpa only [List.nil_append] using h.trans h'

theorem pure_step (l : (composeMachine m g).core.tm.Λ)
    (hn : (composeMachine m g).request l = none)
    (v : (composeMachine m g).core.tm.σ) (S : ∀ k,List ((composeMachine m g).core.tm.Γ k)) :
    Pure m g oracle ⟨some l,v,S⟩
      (stepAux ((composeMachine m g).core.tm.m l) v S) 1 :=
  OracleTM2.Run.ordinary hn rfl (OracleTM2.Run.refl _)

theorem idle_continuation (c : m.Cfg) :
    (composeMachine m g).continuation (idle m.core.tm g.core.tm c) = none := by
  cases h : c.l <;> simp [OracleTM2.continuation,idle,h,caller,composeMachine]

theorem ordinary_run (c d : m.Cfg) (hn : m.continuation c = none)
    (hs : m.core.tm.step c = some d) :
    Pure m g oracle (idle m.core.tm g.core.tm c) (idle m.core.tm g.core.tm d) 1 :=
  OracleTM2.Run.ordinary (idle_continuation m g c)
    (OracleSubstitution.ordinary_step m g.core c d hn hs) (OracleTM2.Run.refl _)

theorem active_continuation (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (c : g.Cfg) :
    (composeMachine m g).continuation (active m.core.tm g.core.tm next v A c) =
      (g.continuation c).map (callee next) := by
  cases h : c.l <;> simp [OracleTM2.continuation,active,h,callee,phase,composeMachine]

theorem active_queryWord (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (c : g.Cfg) :
    (composeMachine m g).queryWord (active m.core.tm g.core.tm next v A c) = g.queryWord c := rfl

theorem active_answer (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (c : g.Cfg) (nextg : g.core.tm.Λ) :
    (composeMachine m g).answerCfg oracle (active m.core.tm g.core.tm next v A c)
      (callee next nextg) =
      active m.core.tm g.core.tm next v A (g.answerCfg oracle c nextg) := by
  apply cfg_ext
  · rfl
  · rfl
  · exact store_update_right m.core.tm g.core.tm A c.stk [] g.answerStack _

/-- Every callee transition, including each genuine nested query and its full
communication charge, is preserved exactly inside the suspended caller. -/
theorem lift_callee_run (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) {c d : g.Cfg} {steps cost : ℕ}
    {qs : OracleTM2.Transcript} (hr : g.Run oracle c d steps cost qs) :
    (composeMachine m g).Run oracle (active m.core.tm g.core.tm next v A c)
      (active m.core.tm g.core.tm next v A d) steps cost qs := by
  induction hr with
  | refl c => exact OracleTM2.Run.refl _
  | @ordinary c d e steps cost qs hn ht hr ih =>
    exact OracleTM2.Run.ordinary (by rw [active_continuation,hn]; rfl)
      (OracleSubstitution.callee_step m g.core next v A c d ht) ih
  | @query c e steps cost qs nextg hq hr ih =>
    rw [←active_answer m g oracle next v A c nextg] at ih
    exact OracleTM2.Run.query (callee next nextg)
      (by rw [active_continuation,hq]; rfl) ih

theorem entry_run' (c : m.Cfg) (next : m.core.tm.Λ)
    (hq : m.continuation c = some next) :
    Pure m g oracle (idle m.core.tm g.core.tm c)
      (stage m g.core .save next c.var c.stk (fun _=>[]) []) 1 :=
  OracleTM2.Run.ordinary (idle_continuation m g c)
    (OracleSubstitution.entry_run m g.core c next hq) (OracleTM2.Run.refl _)

theorem save_protocol (next : m.core.tm.Λ) (v : m.core.tm.σ) (A : ∀ k,List (m.core.tm.Γ k)) :
    Pure m g oracle (stage m g.core .save next v A (fun _=>[]) [])
      (stage m g.core .copy next v (Function.update A m.queryStack []) (fun _=>[])
        ((A m.queryStack).map m.queryAlphabet).reverse) ((A m.queryStack).length+1) := by
  have h := transfer_rel (Pure m g oracle) (@pure_trans m g oracle)
    (.inl m.queryStack) temp (by intro h; cases h) m.queryAlphabet id
    (phase .save next) (phase .copy next)
    (fun v r S => pure_step m g oracle (phase .save next) rfl (v,r) S)
    (v,g.core.tm.initialState) none (store m.core.tm g.core.tm A (fun _=>[]) [])
  simpa [Pure,composeMachine,OracleSubstitution.machine,stage,transferStore,store_update_left,store_update_temp,Function.comp_def] using h

theorem copy_protocol (next : m.core.tm.Λ) (v : m.core.tm.σ) (A : ∀ k,List (m.core.tm.Γ k)) :
    Pure m g oracle
      (stage m g.core .copy next v (Function.update A m.queryStack []) (fun _=>[])
        ((A m.queryStack).map m.queryAlphabet).reverse)
      (stage m g.core .clear next v A
        (pointStack g.core.tm.k₀ (((A m.queryStack).map m.queryAlphabet).map g.core.inputAlphabet.symm)) [])
      ((A m.queryStack).length+1) := by
  have h := transfer₂_rel (Pure m g oracle) (@pure_trans m g oracle)
    temp (.inl m.queryStack) (.inr (.inl g.core.tm.k₀))
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    id m.queryAlphabet.symm g.core.inputAlphabet.symm (phase .copy next) (phase .clear next)
    (fun v r S => pure_step m g oracle (phase .copy next) rfl (v,r) S)
    (v,g.core.tm.initialState) none
    (store m.core.tm g.core.tm (Function.update A m.queryStack []) (fun _=>[])
      ((A m.queryStack).map m.queryAlphabet).reverse)
  simpa [Pure,composeMachine,OracleSubstitution.machine,stage,transfer₂Store,transferStore,store_update_left,store_update_right,
    store_update_temp,Function.comp_def,pointStack,List.map_reverse,List.map_map,
    Function.update_eq_self] using h

theorem clear_protocol (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (q : Bits) :
    Pure m g oracle
      (stage m g.core .clear next v A (pointStack g.core.tm.k₀ (q.map g.core.inputAlphabet.symm)) [])
      (active m.core.tm g.core.tm next v (Function.update A m.answerStack [])
        (g.initial q)) ((A m.answerStack).length+1) := by
  have h := clear_rel (Pure m g oracle) (@pure_trans m g oracle) (.inl m.answerStack)
    (phase .clear next) (callee next g.core.tm.main)
    (fun v r S => pure_step m g oracle (phase .clear next) rfl (v,r) S)
    (v,g.core.tm.initialState) none
    (store m.core.tm g.core.tm A (pointStack g.core.tm.k₀ (q.map g.core.inputAlphabet.symm)) [])
  simpa [Pure,composeMachine,OracleSubstitution.machine,stage,store_update_left,active,OracleTM2.initial,initList_stk] using h

theorem drain_protocol (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (answer : Bits) :
    Pure m g oracle (active m.core.tm g.core.tm next v A (g.final answer))
      (stage m g.core .restore next v A (fun _=>[]) answer.reverse) (answer.length+1) := by
  have h := transfer_rel (Pure m g oracle) (@pure_trans m g oracle)
    (.inr (.inl g.core.tm.k₁)) temp (by intro h; cases h)
    g.core.outputAlphabet id (phase .drain next) (phase .restore next)
    (fun v r S => pure_step m g oracle (phase .drain next) rfl (v,r) S)
    (v,g.core.tm.initialState) none
    (store m.core.tm g.core.tm A (pointStack g.core.tm.k₁ (answer.map g.core.outputAlphabet.symm)) [])
  simpa [Pure,composeMachine,OracleSubstitution.machine,stage,active,OracleTM2.final,haltList_stk,transferStore,store_update_right,
    store_update_temp,pointStack,Function.comp_def,List.map_map,Function.update_eq_self] using h

theorem restore_protocol (next : m.core.tm.Λ) (v : m.core.tm.σ)
    (A : ∀ k,List (m.core.tm.Γ k)) (answer : Bits) :
    Pure m g oracle
      (stage m g.core .restore next v (Function.update A m.answerStack []) (fun _=>[]) answer.reverse)
      (idle m.core.tm g.core.tm ⟨some next,v,
        Function.update A m.answerStack (answer.map m.answerAlphabet.symm)⟩) (answer.length+1) := by
  have h := transfer_rel (Pure m g oracle) (@pure_trans m g oracle)
    temp (.inl m.answerStack) (by intro h; cases h) id m.answerAlphabet.symm
    (phase .restore next) (caller next)
    (fun v r S => pure_step m g oracle (phase .restore next) rfl (v,r) S)
    (v,g.core.tm.initialState) none
    (store m.core.tm g.core.tm (Function.update A m.answerStack []) (fun _=>[]) answer.reverse)
  simpa [Pure,composeMachine,OracleSubstitution.machine,stage,idle,transferStore,store_update_temp,store_update_left,
    Function.comp_def,List.map_reverse] using h

/-- Replacing one caller query preserves the complete callee transcript and
charges every nested oracle communication, in addition to all transfer steps. -/
theorem query_protocol (callerOracle : Bits → Bits) (c : m.Cfg) (next : m.core.tm.Λ)
    (hq : m.continuation c = some next) {s t : ℕ} {qs : OracleTM2.Transcript}
    (hr : g.Run oracle (g.initial (m.queryWord c))
      (g.final (callerOracle (m.queryWord c))) s t qs) :
    (composeMachine m g).Run oracle (idle m.core.tm g.core.tm c)
      (idle m.core.tm g.core.tm (m.answerCfg callerOracle c next))
      (6+(c.stk m.answerStack).length+2*(m.queryWord c).length+
        2*(callerOracle (m.queryWord c)).length+s)
      (6+(c.stk m.answerStack).length+2*(m.queryWord c).length+
        2*(callerOracle (m.queryWord c)).length+t) qs := by
  have h₁ := (entry_run' m g oracle c next hq).trans (save_protocol m g oracle next c.var c.stk)
  have h₂ := h₁.trans (copy_protocol m g oracle next c.var c.stk)
  have h₃ := h₂.trans (clear_protocol m g oracle next c.var c.stk (m.queryWord c))
  have h₄ := h₃.trans (lift_callee_run m g oracle next c.var (Function.update c.stk m.answerStack []) hr)
  have h₅ := h₄.trans (drain_protocol m g oracle next c.var
    (Function.update c.stk m.answerStack []) (callerOracle (m.queryWord c)))
  have h₆ := h₅.trans (restore_protocol m g oracle next c.var c.stk (callerOracle (m.queryWord c)))
  convert h₆ using 1 <;>
    simp only [OracleTM2.queryWord,List.length_map,List.nil_append,List.append_nil] <;> omega

/-- Repeated calls compile to genuine oracle runs. Only caller-valid inputs are
sent to the callee, and every nested query retains the callee's source promise. -/
theorem replace_run {callerOracle : Bits → Bits} (p : Polynomial ℕ)
    (V W : Bits → Prop)
    (outputs : ∀ q, V q → ∃ s t qs,
      g.Run oracle (g.initial q) (g.final (callerOracle q)) s t qs ∧
      t ≤ p.eval q.length ∧ ∀ q a, (q,a) ∈ qs → W q)
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run callerOracle c d steps cost qs) (N : ℕ)
    (hN : ∀ k,(c.stk k).length ≤ N) (valid : ∀ q a,(q,a) ∈ qs → V q) :
    ∃ s t qs', (composeMachine m g).Run oracle
      (idle m.core.tm g.core.tm c) (idle m.core.tm g.core.tm d) s t qs' ∧
      t ≤ cost*(6+N+(machinePushBound m.core.tm+5)*cost+p.eval cost) ∧
      ∀ q a,(q,a) ∈ qs' → W q := by
  apply hr.replacement_run_bound p (composeMachine m g) oracle
    (idle m.core.tm g.core.tm) V W (ordinary_run m g oracle) _ N hN valid
  intro c next hq hvalid
  obtain ⟨s,t,qs,hout,ht,hvs⟩ := outputs (m.queryWord c) hvalid
  exact ⟨_,_,qs,query_protocol m g oracle callerOracle c next hq hout,
    Nat.add_le_add_left ht _,hvs⟩

theorem initial_eq (x : Bits) :
    idle m.core.tm g.core.tm (m.initial x) = (composeMachine m g).initial x :=
  OracleSubstitution.idle_initial m g.core x

theorem final_eq (x : Bits) :
    idle m.core.tm g.core.tm (m.final x) = (composeMachine m g).final x :=
  OracleSubstitution.idle_final m g.core x

theorem initial_length (x : Bits) : ∀ k, ((m.initial x).stk k).length ≤ x.length := by
  intro k
  simp only [OracleTM2.initial,initList]
  split
  · rename_i hk; subst k; simp
  · simp

theorem bound_polynomial (p q : Polynomial ℕ) (N C : ℕ) (hC : C ≤ p.eval N) :
    C*(6+N+(machinePushBound m.core.tm+5)*C+q.eval C) ≤
      (timePolynomial m p q).eval N := by
  have hi : 6+N+(machinePushBound m.core.tm+5)*C+q.eval C ≤
      6+N+(machinePushBound m.core.tm+5)*p.eval N+q.eval (p.eval N) :=
    Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hC) _)
      (natPolynomial_monotone q hC)
  simpa [timePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_comp] using Nat.mul_le_mul hC hi

/-- Transitivity for total binary functions, witnessed by the actual composed
oracle machine, with every nested oracle interface charged at full length. -/
def composeReduction {f g h : Bits → Bits}
    (r : PolyTimeTuringReduction f g) (s : PolyTimeTuringReduction g h) :
    PolyTimeTuringReduction f h where
  machine := composeMachine r.machine s.machine
  time := timePolynomial r.machine r.time s.time
  computes x := by
    obtain ⟨steps,cost,qs,hr,hcost⟩ := r.computes x
    have outputs : ∀ q : Bits, True → ∃ ss tt qss,
        s.machine.Run h (s.machine.initial q) (s.machine.final (g q)) ss tt qss ∧
        tt ≤ s.time.eval q.length ∧ ∀ q a,(q,a) ∈ qss → True := by
      intro q _
      obtain ⟨ss,tt,qss,hh,ht⟩ := s.computes q
      exact ⟨ss,tt,qss,hh,ht,by simp⟩
    obtain ⟨ss,tt,qss,hh,ht,_⟩ := replace_run r.machine s.machine h s.time
      (fun _=>True) (fun _=>True) outputs hr x.length (initial_length r.machine x) (by simp)
    rw [initial_eq,final_eq] at hh
    exact ⟨ss,tt,qss,hh,ht.trans (bound_polynomial r.machine r.time s.time x.length cost hcost)⟩

/-- Transitivity for promised reductions. It works against every extension of
the final source oracle and preserves validity of every actual nested query.
The intermediate oracle is chosen as the problem's specified total value, so no
behavior on invalid inputs is used as advice. -/
def composePromiseReduction {P Q R : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q) (s : PromisePolyTimeTuringReduction Q R) :
    PromisePolyTimeTuringReduction P R where
  machine := composeMachine r.machine s.machine
  time := timePolynomial r.machine r.time s.time
  computes oracle ho x hx := by
    obtain ⟨steps,cost,qs,hr,hcost,hvalid⟩ := r.computes Q.value (fun _ _=>rfl) x hx
    have outputs : ∀ q, Q.valid q → ∃ ss tt qss,
        s.machine.Run oracle (s.machine.initial q) (s.machine.final (Q.value q)) ss tt qss ∧
        tt ≤ s.time.eval q.length ∧ ∀ q a,(q,a) ∈ qss → R.valid q :=
      s.computes oracle ho
    obtain ⟨ss,tt,qss,hh,ht,hvs⟩ := replace_run r.machine s.machine oracle s.time
      Q.valid R.valid outputs hr x.length (initial_length r.machine x) hvalid
    rw [initial_eq,final_eq] at hh
    exact ⟨ss,tt,qss,hh,ht.trans (bound_polynomial r.machine r.time s.time x.length cost hcost),hvs⟩

end

end PlanarHom.OracleReductionComposition

namespace PlanarHom.Complexity

/-- Actual polynomial-time oracle reduction is transitive. -/
noncomputable def PolyTimeTuringReduction.trans {f g h : Bits → Bits}
    (r : PolyTimeTuringReduction f g) (s : PolyTimeTuringReduction g h) :
    PolyTimeTuringReduction f h := OracleReductionComposition.composeReduction r s

/-- The proposition-valued relation inherits the constructed transitivity. -/
theorem TuringReduces.trans {f g h : Bits → Bits}
    (r : TuringReduces f g) (s : TuringReduces g h) : TuringReduces f h := by
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  exact ⟨r.trans s⟩

/-- Promised oracle reductions compose without relying on invalid oracle values. -/
noncomputable def PromisePolyTimeTuringReduction.trans {P Q R : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q) (s : PromisePolyTimeTuringReduction Q R) :
    PromisePolyTimeTuringReduction P R := OracleReductionComposition.composePromiseReduction r s

end PlanarHom.Complexity
