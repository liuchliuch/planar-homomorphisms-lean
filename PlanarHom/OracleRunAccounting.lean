import PlanarHom.OracleAccounting

/-!
# Charged accounting for nested oracle runs

Replacement segments are actual `OracleTM2.Run` derivations, with their complete
nested query transcripts. The resulting run preserves an arbitrary predicate on
every nested query, conditional on validity of the outer queries.
-/

namespace PlanarHom.Complexity.OracleTM2.Run

open PlanarHom.MachineComposition

variable {m : OracleTM2} {callerOracle : Bits → Bits}
variable {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}

/-- Combine actual nested oracle-run segments under a fixed total charge budget
and a stack-size potential, retaining every nested query's validity proof. -/
theorem replacement_run_bound_uniform
    (hr : m.Run callerOracle c d steps cost qs) (p : Polynomial ℕ)
    (n : OracleTM2) (sourceOracle : Bits → Bits) (E : m.Cfg → n.Cfg)
    (V W : Bits → Prop)
    (ordinary : ∀ c d, m.continuation c = none → m.core.tm.step c = some d →
      n.Run sourceOracle (E c) (E d) 1 1 [])
    (query : ∀ c next, m.continuation c = some next → V (m.queryWord c) →
      ∃ s t qs, n.Run sourceOracle (E c) (E (m.answerCfg callerOracle c next)) s t qs ∧
        t ≤ 6 + (c.stk m.answerStack).length + 2 * (m.queryWord c).length +
          2 * (callerOracle (m.queryWord c)).length + p.eval (m.queryWord c).length ∧
        ∀ q a, (q, a) ∈ qs → W q)
    (C L N : ℕ) (hN : ∀ k, (c.stk k).length ≤ N) (hcost : cost ≤ C)
    (hspace : N + (machinePushBound m.core.tm + 1) * cost ≤ L)
    (valid : ∀ q a, (q, a) ∈ qs → V q) :
    ∃ s t qs', n.Run sourceOracle (E c) (E d) s t qs' ∧
      t ≤ steps * (6 + L + 4 * C + p.eval C) ∧
      ∀ q a, (q, a) ∈ qs' → W q := by
  induction hr generalizing N with
  | refl c =>
      exact ⟨0, 0, [], .refl _, by simp, by simp⟩
  | @ordinary c d e steps cost qs hn ht hr ih =>
      have hN' : ∀ k, (d.stk k).length ≤ N + machinePushBound m.core.tm :=
        step_length_le m.core.tm ht N hN
      have hcost' : cost ≤ C := by omega
      have hspace' : N + machinePushBound m.core.tm +
          (machinePushBound m.core.tm + 1) * cost ≤ L := by
        simp only [Nat.mul_add, Nat.mul_one] at hspace
        omega
      obtain ⟨s, t, qs', hrun, hbound, hvalid⟩ :=
        ih (N + machinePushBound m.core.tm) hN' hcost' hspace' valid
      refine ⟨1 + s, 1 + t, qs', ?_, ?_, hvalid⟩
      · simpa using (ordinary c d hn ht).trans hrun
      · rw [Nat.add_mul, Nat.one_mul]
        omega
  | @query c e steps cost qs next hq hr ih =>
      have hN' : ∀ k, ((m.answerCfg callerOracle c next).stk k).length ≤
          N + (callerOracle (m.queryWord c)).length := by
        intro k
        by_cases hk : k = m.answerStack
        · subst k
          simp only [OracleTM2.answerCfg, Function.update_self, List.length_map]
          omega
        · simpa [OracleTM2.answerCfg, Function.update_of_ne hk] using
            (hN k).trans (Nat.le_add_right N (callerOracle (m.queryWord c)).length)
      have hcost' : cost ≤ C := by omega
      have hspace' : N + (callerOracle (m.queryWord c)).length +
          (machinePushBound m.core.tm + 1) * cost ≤ L := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hspace ⊢
        omega
      have valid' : ∀ q a, (q, a) ∈ qs → V q := by
        intro q a hqa
        exact valid q a (List.mem_cons_of_mem _ hqa)
      have validHead : V (m.queryWord c) :=
        valid _ _ (List.mem_cons_self ..)
      obtain ⟨s, t, qs', hrun, hbound, hvalid⟩ :=
        ih (N + (callerOracle (m.queryWord c)).length) hN' hcost' hspace' valid'
      obtain ⟨sq, tq, qq, hquery, ht, hqvalid⟩ := query c next hq validHead
      have hqcost : (m.queryWord c).length ≤ C := by omega
      have hacost : (callerOracle (m.queryWord c)).length ≤ C := by omega
      have hpoly : p.eval (m.queryWord c).length ≤ p.eval C :=
        natPolynomial_monotone p hqcost
      have hanswer : (c.stk m.answerStack).length ≤ L := by
        have ha := hN m.answerStack
        omega
      have htbound : tq ≤ 6 + L + 4 * C + p.eval C := by omega
      refine ⟨sq + s, tq + t, qq ++ qs', hquery.trans hrun, ?_, ?_⟩
      · rw [Nat.add_mul, Nat.one_mul]
        omega
      · intro q a hqa
        rcases List.mem_append.mp hqa with hqa | hqa
        · exact hqvalid q a hqa
        · exact hvalid q a hqa

/-- Replacement by genuine charged oracle runs is polynomially bounded and
preserves promised validity of every query in the combined nested transcript. -/
theorem replacement_run_bound
    (hr : m.Run callerOracle c d steps cost qs) (p : Polynomial ℕ)
    (n : OracleTM2) (sourceOracle : Bits → Bits) (E : m.Cfg → n.Cfg)
    (V W : Bits → Prop)
    (ordinary : ∀ c d, m.continuation c = none → m.core.tm.step c = some d →
      n.Run sourceOracle (E c) (E d) 1 1 [])
    (query : ∀ c next, m.continuation c = some next → V (m.queryWord c) →
      ∃ s t qs, n.Run sourceOracle (E c) (E (m.answerCfg callerOracle c next)) s t qs ∧
        t ≤ 6 + (c.stk m.answerStack).length + 2 * (m.queryWord c).length +
          2 * (callerOracle (m.queryWord c)).length + p.eval (m.queryWord c).length ∧
        ∀ q a, (q, a) ∈ qs → W q)
    (N : ℕ) (hN : ∀ k, (c.stk k).length ≤ N)
    (valid : ∀ q a, (q, a) ∈ qs → V q) :
    ∃ s t qs', n.Run sourceOracle (E c) (E d) s t qs' ∧
      t ≤ cost * (6 + N + (machinePushBound m.core.tm + 5) * cost + p.eval cost) ∧
      ∀ q a, (q, a) ∈ qs' → W q := by
  obtain ⟨s, t, qs', hrun, ht, hvalid⟩ := replacement_run_bound_uniform
    hr p n sourceOracle E V W ordinary query cost
    (N + (machinePushBound m.core.tm + 1) * cost) N hN (Nat.le_refl _) (Nat.le_refl _) valid
  refine ⟨s, t, qs', hrun, ?_, hvalid⟩
  have hb := ht.trans (Nat.mul_le_mul_right _ hr.steps_le)
  have heq : 6 + (N + (machinePushBound m.core.tm + 1) * cost) + 4 * cost + p.eval cost =
      6 + N + (machinePushBound m.core.tm + 5) * cost + p.eval cost := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  rw [heq] at hb
  exact hb

end PlanarHom.Complexity.OracleTM2.Run
