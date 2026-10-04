import PlanarHom.BooleanNormSampleCompleteness

open PlanarHom PlanarHom.BooleanNormSampleSearch
open PlanarHom.Complexity PlanarHom.ArithmeticCircuitPrimitives

example : grid 3 = [3/4,1/2,1/4] := by
  norm_num [grid, List.range_succ, BooleanExceptionalGrid.rationalSample]

example : candidates 0 (fun _ => true) (3,(0,[])) = [] := by
  norm_num [candidates,accept,pairs,ExponentVectors.box,grid,List.range_succ]

example (c w : Fin 1 → ℚ) (p : Input) :
    BooleanNormSampleMachines.candidates c (fun _ => 0) w p = grid p.1 := by
  simp [BooleanNormSampleMachines.candidates,candidates,accept,
    BooleanNormSampleMachines.bad,BooleanNormSampleMachines.eligible]

example {b : ℕ} (c a w : Fin b → ℚ) (N : ℕ) (ns : List ℕ) :
    BooleanNormSampleMachines.candidates c a w (N,(0,ns)) = grid N := by
  simp [BooleanNormSampleMachines.candidates,candidates,accept,
    BooleanNormSampleMachines.bad,BooleanNormSampleMachines.eligible,
    BooleanNormSampleMachines.leftCounts,BooleanNormSampleMachines.rightCounts,
    BooleanNormSampleMachines.counts]

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {d b : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (c a w : Fin b → K) :
    FP inputEncoding BitEncoding.rat.list (BooleanNormSampleMachines.candidates c a w) :=
  BooleanNormSampleMachines.fp_candidates basis c a w

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b : ℕ}
    (c a w : Fin b → K) (p : Input) (q : ℚ)
    (hq : q ∈ BooleanNormSampleMachines.candidates c a w p)
    (k l : Fin b → ℕ)
    (hk : ∀ i, k i ≤ BooleanNormSampleMachines.counts p i)
    (hl : ∀ i, l i ≤ BooleanNormSampleMachines.counts p i)
    (hdiff : ∃ i, a i ≠ 0 ∧ k i ≠ l i) :
    BooleanFieldCollision.collision c a w (algebraMap ℚ K q)
      (BooleanNormSampleMachines.counts p) k l ≠ 0 :=
  BooleanNormSampleCompleteness.candidate_norm_ne_zero c a w p q hq k l hk hl hdiff
