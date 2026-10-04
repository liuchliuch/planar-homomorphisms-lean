import PlanarHom.Complexity

/-!
# Accounting for genuine replacements of oracle transitions

This file is independent of any particular compiler. Given proved executions of
ordinary instructions and query replacement protocols, it combines those real
executions and bounds their total number of transitions. Query and answer words
are charged at their full materialized lengths.
-/

namespace PlanarHom.Complexity.OracleTM2.Run

open PlanarHom.MachineComposition

variable {m : OracleTM2} {oracle : Bits → Bits} {B : Type}
variable {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}

/-- A uniform replacement bound with a fixed total charge budget and stack-size
potential. The stronger transition-count factor is useful before applying
`Run.steps_le`. -/
theorem replacement_bound_uniform
    (hr : m.Run oracle c d steps cost qs) (p : Polynomial ℕ)
    (F : B → Option B) (E : m.Cfg → B)
    (ordinary : ∀ c d, m.continuation c = none → m.core.tm.step c = some d →
      F (E c) = some (E d))
    (query : ∀ c next, m.continuation c = some next →
      ∃ n, n ≤ 6 + (c.stk m.answerStack).length + 2 * (m.queryWord c).length +
          2 * (oracle (m.queryWord c)).length + p.eval (m.queryWord c).length ∧
        (fun x : Option B => x.bind F)^[n] (some (E c)) =
          some (E (m.answerCfg oracle c next)))
    (C L N : ℕ) (hN : ∀ k, (c.stk k).length ≤ N) (hcost : cost ≤ C)
    (hspace : N + (machinePushBound m.core.tm + 1) * cost ≤ L) :
    ∃ n, n ≤ steps * (6 + L + 4 * C + p.eval C) ∧
      (fun x : Option B => x.bind F)^[n] (some (E c)) = some (E d) := by
  induction hr generalizing N with
  | refl c => exact ⟨0, by simp, rfl⟩
  | @ordinary c d e steps cost qs hn ht hr ih =>
      have hN' : ∀ k, (d.stk k).length ≤ N + machinePushBound m.core.tm :=
        step_length_le m.core.tm ht N hN
      have hcost' : cost ≤ C := by omega
      have hspace' : N + machinePushBound m.core.tm +
          (machinePushBound m.core.tm + 1) * cost ≤ L := by
        simp only [Nat.mul_add, Nat.mul_one] at hspace
        omega
      obtain ⟨n, hbound, hrun⟩ := ih (N + machinePushBound m.core.tm) hN' hcost' hspace'
      refine ⟨n + 1, ?_, ?_⟩
      · rw [Nat.add_mul, Nat.one_mul]
        omega
      · rw [Function.iterate_succ_apply]
        change (fun x : Option B => x.bind F)^[n] (F (E c)) = some (E e)
        rw [ordinary c d hn ht]
        exact hrun
  | @query c e steps cost qs next hq hr ih =>
      have hN' : ∀ k, ((m.answerCfg oracle c next).stk k).length ≤
          N + (oracle (m.queryWord c)).length := by
        intro k
        by_cases hk : k = m.answerStack
        · subst k
          simp only [OracleTM2.answerCfg, Function.update_self, List.length_map]
          omega
        · simpa [OracleTM2.answerCfg, Function.update_of_ne hk] using
            (hN k).trans (Nat.le_add_right N (oracle (m.queryWord c)).length)
      have hcost' : cost ≤ C := by omega
      have hspace' : N + (oracle (m.queryWord c)).length +
          (machinePushBound m.core.tm + 1) * cost ≤ L := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hspace ⊢
        omega
      obtain ⟨n, hbound, hrun⟩ :=
        ih (N + (oracle (m.queryWord c)).length) hN' hcost' hspace'
      obtain ⟨t, ht, hquery⟩ := query c next hq
      have hqcost : (m.queryWord c).length ≤ C := by omega
      have hacost : (oracle (m.queryWord c)).length ≤ C := by omega
      have hpoly : p.eval (m.queryWord c).length ≤ p.eval C :=
        natPolynomial_monotone p hqcost
      have hanswer : (c.stk m.answerStack).length ≤ L := by
        have ha := hN m.answerStack
        omega
      have htbound : t ≤ 6 + L + 4 * C + p.eval C := by omega
      refine ⟨n + t, ?_, ?_⟩
      · rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add hbound htbound
      · rw [Function.iterate_add_apply, hquery, hrun]

/-- Replace every oracle transition by its proved finite execution and bound the
resulting actual iterator. The ordinary machine's fixed syntax supplies the
stack-growth constant; oracle answers contribute their fully charged lengths. -/
theorem replacement_bound
    (hr : m.Run oracle c d steps cost qs) (p : Polynomial ℕ)
    (F : B → Option B) (E : m.Cfg → B)
    (ordinary : ∀ c d, m.continuation c = none → m.core.tm.step c = some d →
      F (E c) = some (E d))
    (query : ∀ c next, m.continuation c = some next →
      ∃ n, n ≤ 6 + (c.stk m.answerStack).length + 2 * (m.queryWord c).length +
          2 * (oracle (m.queryWord c)).length + p.eval (m.queryWord c).length ∧
        (fun x : Option B => x.bind F)^[n] (some (E c)) =
          some (E (m.answerCfg oracle c next)))
    (N : ℕ) (hN : ∀ k, (c.stk k).length ≤ N) :
    ∃ n, n ≤ cost * (6 + N + (machinePushBound m.core.tm + 5) * cost + p.eval cost) ∧
      (fun x : Option B => x.bind F)^[n] (some (E c)) = some (E d) := by
  obtain ⟨n, hn, hrun⟩ := replacement_bound_uniform hr p F E ordinary query
    cost (N + (machinePushBound m.core.tm + 1) * cost) N hN (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨n, ?_, hrun⟩
  have hb := hn.trans (Nat.mul_le_mul_right _ hr.steps_le)
  have heq : 6 + (N + (machinePushBound m.core.tm + 1) * cost) + 4 * cost + p.eval cost =
      6 + N + (machinePushBound m.core.tm + 5) * cost + p.eval cost := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  rw [heq] at hb
  exact hb

end PlanarHom.Complexity.OracleTM2.Run
