import PlanarHom.OracleReductionComposition

/-! Output-space bounds for actual bit-charged oracle runs. -/
namespace PlanarHom.Complexity.OracleTM2.Run
open PlanarHom.MachineComposition

theorem stack_length_bound {m : OracleTM2} {oracle : Bits→Bits}
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle c d steps cost qs) (N : ℕ) (hN : ∀k,(c.stk k).length≤N) :
    ∀k,(d.stk k).length≤N+(machinePushBound m.core.tm+1)*cost:=by
  induction hr generalizing N with
  | refl c=>simpa using hN
  | @ordinary c d e steps cost qs hn ht hr ih=>
    have hs:=step_length_le m.core.tm ht N hN
    intro k
    have hh:=ih (N+machinePushBound m.core.tm) hs k
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  | @query c e steps cost qs next hq hr ih=>
    have hs : ∀k,((m.answerCfg oracle c next).stk k).length≤N+(oracle (m.queryWord c)).length:=by
      intro k
      by_cases hk:k=m.answerStack
      · subst k
        simp only [OracleTM2.answerCfg,Function.update_self,List.length_map]
        omega
      · simpa [OracleTM2.answerCfg,Function.update_of_ne hk] using
          (hN k).trans (Nat.le_add_right N (oracle (m.queryWord c)).length)
    intro k
    have hh:=ih (N+(oracle (m.queryWord c)).length) hs k
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at hh ⊢
    omega

theorem output_length_bound {m : OracleTM2} {oracle : Bits→Bits} {input output : Bits}
    {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle (m.initial input) (m.final output) steps cost qs) :
    output.length≤ input.length+(machinePushBound m.core.tm+1)*cost:=by
  have h:=hr.stack_length_bound input.length (PlanarHom.OracleReductionComposition.initial_length m input) m.core.tm.k₁
  simpa [OracleTM2.final,Turing.haltList] using h

end PlanarHom.Complexity.OracleTM2.Run
