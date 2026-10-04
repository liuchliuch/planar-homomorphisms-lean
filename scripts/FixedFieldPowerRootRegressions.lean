import PlanarHom.FixedFieldOddPowerRootMachines

open PlanarHom Complexity FixedFieldPowerRootCandidates

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (n : ℕ) :
    FP (numberFieldEncoding b) (numberFieldEncoding b).list (roots b n) := fp_roots b n

-- The exact list specification covers every root, including zero and both signs.
example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (x : K) :
    x ∈ roots b 2 (x^2) ∧ -x ∈ roots b 2 (x^2) := by
  constructor
  · exact (mem_roots_iff b 2 (by decide) x _).mpr rfl
  · apply (mem_roots_iff b 2 (by decide) (-x) _).mpr
    ring

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (n : ℕ) (hn : 0 < n) :
    (0:K) ∈ roots b n 0 := by
  apply (mem_roots_iff b n hn 0 0).mpr
  exact zero_pow hn.ne'

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (x y : K) (h : x^2 ≠ y) :
    x ∉ roots b 2 y := by simpa only [mem_roots_iff b 2 (by decide) x y] using h

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (e : K →+* ℝ) (x : K) :
    FixedFieldOddPowerRootMachines.root b 3 (x^3) = x :=
  FixedFieldOddPowerRootMachines.root_pow b e 3 (by decide) x

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (e : K →+* ℝ) (x : K) :
    FixedFieldOddPowerRootMachines.root b 1 x = x := by
  simpa using FixedFieldOddPowerRootMachines.root_pow b e 1 (by decide) x
