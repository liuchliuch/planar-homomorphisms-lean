import PlanarHom.OraclePrecomposition

/-! Actual ordinary postprocessing of a finite oracle computation, preserving
all oracle queries and charging the exact additional TM2 transitions. -/
namespace PlanarHom.MachineComposition.StackEmbedding
open Turing.TM2

theorem representsEmpty_update {K J : Type} {Γ : K→Type} {Δ : J→Type}
    [DecidableEq K] [DecidableEq J] (e : StackEmbedding Γ Δ)
    {S : ∀k,List (Γ k)} {T : ∀j,List (Δ j)} (h : e.RepresentsEmpty S T)
    (k : K) (xs : List (Γ k)) :
    e.RepresentsEmpty (Function.update S k xs)
      (Function.update T (e.index k) (xs.map (e.alphabet k))):=by
  refine ⟨e.represents_update h.1 k xs,?_⟩
  intro j hj
  rw [Function.update_of_ne (hj k)]
  exact h.2 j hj

end PlanarHom.MachineComposition.StackEmbedding

namespace PlanarHom.OraclePostcomposition
noncomputable section
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

variable (a : OracleTM2) (b : TM2ComputableAux Bool Bool)

def alphabet : a.core.tm.Γ a.core.tm.k₁ ≃ b.tm.Γ b.tm.k₀:=
  a.core.outputAlphabet.trans b.inputAlphabet.symm

def embedding : StackEmbedding a.core.tm.Γ (sharedAlphabet a.core.tm.k₁ a.core.tm.Γ b.tm.Γ):=
  leftEmbedding a.core.tm.k₁ b.tm.k₀ (alphabet a b)

def machine [∀k,Fintype (b.tm.Γ k)] : OracleTM2:=by
  letI : ∀k,Fintype (a.core.tm.Γ k):=a.finiteAlphabet
  let e:=embedding a b
  exact {
    core:={
      tm:=sequentialMachine a.core.tm b.tm (alphabet a b)
      inputAlphabet:=(e.alphabet a.core.tm.k₀).symm.trans a.core.inputAlphabet
      outputAlphabet:=b.outputAlphabet }
    finiteAlphabet:=sequentialAlphabetFintype a.core.tm b.tm (alphabet a b)
    queryStack:=e.index a.queryStack
    answerStack:=e.index a.answerStack
    queryAlphabet:=(e.alphabet a.queryStack).symm.trans a.queryAlphabet
    answerAlphabet:=(e.alphabet a.answerStack).symm.trans a.answerAlphabet
    request:=Sum.elim (fun l=>(a.request l).map Sum.inl) (fun _=>none) }

variable [∀k,Fintype (b.tm.Γ k)]

private theorem left_continuation {c : a.Cfg} {d : (machine a b).Cfg}
    (h : LeftRel a.core.tm b.tm (alphabet a b) c d) :
    (machine a b).continuation d=(a.continuation c).map Sum.inl:=by
  unfold OracleTM2.continuation
  rw [h.1]
  cases c.l <;> rfl

private theorem left_queryWord {c : a.Cfg} {d : (machine a b).Cfg}
    (h : LeftRel a.core.tm b.tm (alphabet a b) c d) :
    (machine a b).queryWord d=a.queryWord c:=by
  change (d.stk ((embedding a b).index a.queryStack)).map
    (((embedding a b).alphabet a.queryStack).symm.trans a.queryAlphabet)=_
  dsimp only [embedding]
  rw [h.2.2.1 a.queryStack]
  simp only [List.map_map,Equiv.trans_apply,Equiv.symm_apply_apply,Function.comp_def,OracleTM2.queryWord]

private theorem left_answer {oracle : Bits→Bits} {c : a.Cfg} {d : (machine a b).Cfg}
    (h : LeftRel a.core.tm b.tm (alphabet a b) c d) (next : a.core.tm.Λ) :
    LeftRel a.core.tm b.tm (alphabet a b) (a.answerCfg oracle c next)
      ((machine a b).answerCfg oracle d (.inl next)):=by
  refine ⟨rfl,h.2.1,?_⟩
  have hs:=(embedding a b).representsEmpty_update h.2.2 a.answerStack
    ((oracle (a.queryWord c)).map a.answerAlphabet.symm)
  change (embedding a b).RepresentsEmpty
    (Function.update c.stk a.answerStack ((oracle (a.queryWord c)).map a.answerAlphabet.symm))
    (Function.update d.stk ((embedding a b).index a.answerStack)
      ((oracle ((machine a b).queryWord d)).map
        (((embedding a b).alphabet a.answerStack).symm.trans a.answerAlphabet).symm))
  rw [left_queryWord a b h]
  simpa only [List.map_map,Equiv.symm_trans_apply,Equiv.symm_symm,Function.comp_def] using hs

/-- The oracle phase is embedded with unchanged communication and transcript. -/
theorem left_run {oracle : Bits→Bits} {c z : a.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : a.Run oracle c z steps cost qs) (d : (machine a b).Cfg)
    (hd : LeftRel a.core.tm b.tm (alphabet a b) c d) :
    ∃e,(machine a b).Run oracle d e steps cost qs ∧ LeftRel a.core.tm b.tm (alphabet a b) z e:=by
  induction hr generalizing d with
  | refl c=>exact ⟨d,.refl d,hd⟩
  | @ordinary c c' z steps cost qs hn ht hr ih=>
    obtain ⟨d',ht',hd'⟩:=sequential_left_step a.core.tm b.tm (alphabet a b) c c' d ht hd
    obtain ⟨e,he,hrel⟩:=ih d' hd'
    refine ⟨e,.ordinary ?_ ht' he,hrel⟩
    rw [left_continuation a b hd,hn]
    rfl
  | @query c z steps cost qs next hq hr ih=>
    obtain ⟨e,he,hrel⟩:=ih ((machine a b).answerCfg oracle d (.inl next)) (left_answer a b hd next)
    have hq' : (machine a b).continuation d=some (.inl next):=by rw [left_continuation a b hd,hq]; rfl
    refine ⟨e,?_,hrel⟩
    have hh:=OracleTM2.Run.query (m:=machine a b) (oracle:=oracle) (.inl next) hq' he
    simpa only [left_queryWord a b hd] using hh

private theorem right_continuation {c : b.tm.Cfg} {d : (machine a b).Cfg}
    (h : RightRel a.core.tm b.tm (alphabet a b) c d) :
    (machine a b).continuation d=none:=by
  unfold OracleTM2.continuation
  rw [h.1]
  cases c.l <;> rfl

theorem right_run {oracle : Bits→Bits} (n : ℕ) (c z : b.tm.Cfg)
    (h : (fun x : Option b.tm.Cfg=>x.bind b.tm.step)^[n] (some c)=some z)
    (d : (machine a b).Cfg) (hd : RightRel a.core.tm b.tm (alphabet a b) c d) :
    ∃e,(machine a b).Run oracle d e n n [] ∧ RightRel a.core.tm b.tm (alphabet a b) z e:=by
  induction n generalizing c d with
  | zero=>have hc:c=z:=Option.some.inj h; subst z; exact ⟨d,.refl d,hd⟩
  | succ n ih=>
    rw [Function.iterate_succ_apply] at h
    change (fun x : Option b.tm.Cfg=>x.bind b.tm.step)^[n] (b.tm.step c)=some z at h
    cases hs:b.tm.step c with
    | none=>
      rw [hs] at h
      have hf : (fun x : Option b.tm.Cfg=>x.bind b.tm.step)^[n] none=none:=Function.iterate_fixed rfl n
      rw [hf] at h
      contradiction
    | some c'=>
      rw [hs] at h
      obtain ⟨d',hstep,hrel⟩:=sequential_right_step a.core.tm b.tm (alphabet a b) c c' d hs hd
      obtain ⟨e,he,hz⟩:=ih c' h d' hrel
      exact ⟨e,.ordinary (right_continuation a b hd) hstep he,hz⟩

private theorem initial (x : Bits) :
    LeftRel a.core.tm b.tm (alphabet a b) (a.initial x) ((machine a b).initial x):=by
  have h:=sequential_initial a.core.tm b.tm (alphabet a b) (x.map a.core.inputAlphabet.symm)
  simpa only [machine,OracleTM2.initial,List.map_map,Equiv.symm_trans_apply,
    Equiv.symm_symm,Function.comp_def,embedding] using h

/-- Complete oracle execution followed by the actual exact-output postprocessor. -/
theorem run {oracle : Bits→Bits} (x y z : Bits) {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : a.Run oracle (a.initial x) (a.final y) steps cost qs) (time : ℕ)
    (out : TM2OutputsInTime b.tm (y.map b.inputAlphabet.symm)
      (some (z.map b.outputAlphabet.symm)) time) :
    (machine a b).Run oracle ((machine a b).initial x) ((machine a b).final z)
      (steps+out.steps) (cost+out.steps) qs:=by
  obtain ⟨d,hd,hrel⟩:=left_run a b hr _ (initial a b x)
  have hh:=sequential_handoff a.core.tm b.tm (alphabet a b) (y.map a.core.outputAlphabet.symm) d hrel
  have hh' : RightRel a.core.tm b.tm (alphabet a b) (initList b.tm (y.map b.inputAlphabet.symm)) d:=by
    simpa only [alphabet,List.map_map,Function.comp_def,Equiv.trans_apply,Equiv.apply_symm_apply] using hh
  obtain ⟨e,he,hfinal⟩:=right_run a b out.steps _ _ out.evals_in_steps d hh'
  have heq : e=(machine a b).final z:=sequential_final a.core.tm b.tm (alphabet a b)
    (z.map b.outputAlphabet.symm) e hfinal
  subst e
  simpa only [List.append_nil] using hd.trans he

end
end PlanarHom.OraclePostcomposition
