import PlanarHom.AlgebraicRealApproximationMachines

open PlanarHom Complexity AlgebraicRealApproximationAlgorithm

example : grid 0 2 10 3 = (3/5:ℚ) := by norm_num [grid]
example : grid (-3) 7 13 0 = -3 := grid_zero _ _ _
example : grid (-3) 7 13 13 = 7 := grid_self _ _ _ (by decide)
example : grid (-3) 7 0 29 = -3 := by norm_num [grid]

example : approximate (Polynomial.X : Polynomial ℚ) (-1) 1 2 = 0 := by
  have hi : index (Polynomial.X : Polynomial ℚ) (-1) 1 2 = 1 := by
    apply IntervalBisection.cut_eq
    · intro t ht
      interval_cases t <;> norm_num [test, grid]
    · omega
  rw [approximate, hi]
  norm_num [grid]

example (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ∃ f : ℕ → ℚ, FP BitEncoding.nat BitEncoding.rat f ∧
      ∀ N : ℕ, |(f N : ℝ)-a| ≤ 1/((N:ℝ)+1) :=
  AlgebraicRealApproximationMachines.exists_fp_approximation a ha

example (p : Polynomial ℚ) (l u : ℚ) :
    FP BitEncoding.nat BitEncoding.rat (approximate p l u) :=
  AlgebraicRealApproximationMachines.fp_approximate p l u
