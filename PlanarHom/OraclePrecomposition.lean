import PlanarHom.OracleSubstitution

/-! Actual sequential composition of an ordinary finite-alphabet preprocessor
with an oracle machine. All query words, answers and transcript costs are kept. -/
namespace PlanarHom.OraclePrecomposition
noncomputable section
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

variable (a : TM2ComputableAux Bool Bool) (b : OracleTM2)

def alphabet : a.tm.Γ a.tm.k₁ ≃ b.core.tm.Γ b.core.tm.k₀:=
  a.outputAlphabet.trans b.core.inputAlphabet.symm

def machine [∀k,Fintype (a.tm.Γ k)] : OracleTM2:=by
  letI : ∀k,Fintype (b.core.tm.Γ k):=b.finiteAlphabet
  let e:=leftEmbedding a.tm.k₁ b.core.tm.k₀ (alphabet a b)
  exact {
    core:={
      tm:=sequentialMachine a.tm b.core.tm (alphabet a b)
      inputAlphabet:=(e.alphabet a.tm.k₀).symm.trans a.inputAlphabet
      outputAlphabet:=b.core.outputAlphabet }
    finiteAlphabet:=sequentialAlphabetFintype a.tm b.core.tm (alphabet a b)
    queryStack:=.inr b.queryStack
    answerStack:=.inr b.answerStack
    queryAlphabet:=b.queryAlphabet
    answerAlphabet:=b.answerAlphabet
    request:=Sum.elim (fun _=>none) (fun l=>(b.request l).map Sum.inr) }

variable [∀k,Fintype (a.tm.Γ k)]

private theorem right_stack {c : b.Cfg} {d : (machine a b).Cfg}
    (h : RightRel a.tm b.core.tm (alphabet a b) c d) (k : b.core.tm.K) :
    d.stk (.inr k)=c.stk k:=by
  have hs:=h.2.2.1 k
  change d.stk (.inr k)=(c.stk k).map id at hs
  simpa only [List.map_id] using hs

private theorem right_continuation {c : b.Cfg} {d : (machine a b).Cfg}
    (h : RightRel a.tm b.core.tm (alphabet a b) c d) :
    (machine a b).continuation d=(b.continuation c).map Sum.inr:=by
  unfold OracleTM2.continuation
  rw [h.1]
  cases c.l <;> rfl

private theorem right_queryWord {c : b.Cfg} {d : (machine a b).Cfg}
    (h : RightRel a.tm b.core.tm (alphabet a b) c d) :
    (machine a b).queryWord d=b.queryWord c:=by
  change (d.stk (.inr b.queryStack)).map b.queryAlphabet=_
  rw [right_stack a b h]
  rfl

private theorem right_answer {oracle : Bits→Bits} {c : b.Cfg} {d : (machine a b).Cfg}
    (h : RightRel a.tm b.core.tm (alphabet a b) c d) (next : b.core.tm.Λ) :
    RightRel a.tm b.core.tm (alphabet a b) (b.answerCfg oracle c next)
      ((machine a b).answerCfg oracle d (.inr next)):=by
  refine ⟨rfl,h.2.1,?_,?_⟩
  · intro k
    change Function.update d.stk (.inr b.answerStack)
      ((oracle ((machine a b).queryWord d)).map b.answerAlphabet.symm) (.inr k)=
        List.map (Equiv.refl _) (Function.update c.stk b.answerStack
          ((oracle (b.queryWord c)).map b.answerAlphabet.symm) k)
    rw [right_queryWord a b h]
    by_cases hk:k=b.answerStack
    · subst k
      simp
    · simp only [Function.update_of_ne hk,Function.update_of_ne (show Sum.inr k≠(Sum.inr b.answerStack : SharedBank a.tm.k₁ b.core.tm.K) by simpa using hk)]
      change d.stk (.inr k)=(c.stk k).map id
      simpa only [List.map_id] using right_stack a b h k
  · intro k hk
    cases k with
    | inl k=>
      change Function.update d.stk (.inr b.answerStack)
        ((oracle ((machine a b).queryWord d)).map b.answerAlphabet.symm) (.inl k)=[]
      rw [Function.update_of_ne (by simp)]
      exact h.2.2.2 (.inl k) (by intro j; simp [rightEmbedding])
    | inr k=>exact False.elim (hk k rfl)

/-- Every oracle transition in the second phase is copied exactly, including
its complete charged query and answer and its original transcript entry. -/
theorem right_run {oracle : Bits→Bits} {c z : b.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : b.Run oracle c z steps cost qs) (d : (machine a b).Cfg)
    (hd : RightRel a.tm b.core.tm (alphabet a b) c d) :
    ∃e,(machine a b).Run oracle d e steps cost qs ∧ RightRel a.tm b.core.tm (alphabet a b) z e:=by
  induction hr generalizing d with
  | refl c=>exact ⟨d,.refl d,hd⟩
  | @ordinary c c' z steps cost qs hn ht hr ih=>
    obtain ⟨d',ht',hd'⟩:=sequential_right_step a.tm b.core.tm (alphabet a b) c c' d ht hd
    obtain ⟨e,he,hrel⟩:=ih d' hd'
    refine ⟨e,.ordinary ?_ ht' he,hrel⟩
    rw [right_continuation a b hd,hn]
    rfl
  | @query c z steps cost qs next hq hr ih=>
    obtain ⟨e,he,hrel⟩:=ih ((machine a b).answerCfg oracle d (.inr next)) (right_answer a b hd next)
    have hq' : (machine a b).continuation d=some (.inr next):=by rw [right_continuation a b hd,hq]; rfl
    refine ⟨e,?_,hrel⟩
    have hh:=OracleTM2.Run.query (m:=machine a b) (oracle:=oracle) (.inr next) hq' he
    simpa only [right_queryWord a b hd] using hh

private theorem left_continuation {c c' : a.tm.Cfg} {d : (machine a b).Cfg}
    (hc : a.tm.step c=some c') (h : LeftRel a.tm b.core.tm (alphabet a b) c d) :
    (machine a b).continuation d=none:=by
  rcases c with ⟨cl,cv,C⟩
  cases cl with
  | none=>simp [FinTM2.step,step] at hc
  | some l=>
    unfold OracleTM2.continuation
    rw [h.1]
    rfl

/-- Ordinary preprocessing is simulated one-for-one before any oracle label
is active. The exact original number of transitions is retained. -/
theorem left_run {oracle : Bits→Bits} (n : ℕ) (c z : a.tm.Cfg)
    (h : (fun x : Option a.tm.Cfg=>x.bind a.tm.step)^[n] (some c)=some z)
    (d : (machine a b).Cfg) (hd : LeftRel a.tm b.core.tm (alphabet a b) c d) :
    ∃e,(machine a b).Run oracle d e n n [] ∧ LeftRel a.tm b.core.tm (alphabet a b) z e:=by
  induction n generalizing c d with
  | zero=>have hc:c=z:=Option.some.inj h; subst z; exact ⟨d,.refl d,hd⟩
  | succ n ih=>
    rw [Function.iterate_succ_apply] at h
    change (fun x : Option a.tm.Cfg=>x.bind a.tm.step)^[n] (a.tm.step c)=some z at h
    cases hs:a.tm.step c with
    | none=>
      rw [hs] at h
      have hf : (fun x : Option a.tm.Cfg=>x.bind a.tm.step)^[n] none=none:=
        Function.iterate_fixed rfl n
      rw [hf] at h
      contradiction
    | some c'=>
      rw [hs] at h
      obtain ⟨d',hstep,hrel⟩:=sequential_left_step a.tm b.core.tm (alphabet a b) c c' d hs hd
      obtain ⟨e,he,hz⟩:=ih c' h d' hrel
      exact ⟨e,.ordinary (left_continuation a b hs hd) hstep he,hz⟩

private theorem initial (x : Bits) :
    LeftRel a.tm b.core.tm (alphabet a b) (initList a.tm (x.map a.inputAlphabet.symm))
      ((machine a b).initial x):=by
  have h:=sequential_initial a.tm b.core.tm (alphabet a b) (x.map a.inputAlphabet.symm)
  simpa only [machine,OracleTM2.initial,List.map_map,Equiv.symm_trans_apply,
    Equiv.symm_symm,Function.comp_def] using h

/-- Complete finite preprocessing plus an arbitrary genuine oracle run. -/
theorem run {oracle : Bits→Bits} (x y z : Bits) (time : ℕ)
    (out : TM2OutputsInTime a.tm (x.map a.inputAlphabet.symm)
      (some (y.map a.outputAlphabet.symm)) time)
    {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : b.Run oracle (b.initial y) (b.final z) steps cost qs) :
    (machine a b).Run oracle ((machine a b).initial x) ((machine a b).final z)
      (out.steps+steps) (out.steps+cost) qs:=by
  obtain ⟨d,hd,hrel⟩:=left_run a b out.steps _ _ out.evals_in_steps _ (initial a b x)
  have hh:=sequential_handoff a.tm b.core.tm (alphabet a b) (y.map a.outputAlphabet.symm) d hrel
  have hh' : RightRel a.tm b.core.tm (alphabet a b) (b.initial y) d:=by
    simpa only [alphabet,OracleTM2.initial,List.map_map,Function.comp_def,Equiv.trans_apply,
      Equiv.apply_symm_apply] using hh
  obtain ⟨e,he,hfinal⟩:=right_run a b hr d hh'
  have heq : e=(machine a b).final z:=sequential_final a.tm b.core.tm (alphabet a b)
    (z.map b.core.outputAlphabet.symm) e hfinal
  subst e
  simpa only [List.nil_append] using hd.trans he

end
end PlanarHom.OraclePrecomposition
