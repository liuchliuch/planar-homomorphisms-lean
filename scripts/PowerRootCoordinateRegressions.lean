import PlanarHom.PowerRootCoordinateMachines

open PlanarHom Complexity PowerRootCoordinateAnnihilator PowerRootCoordinateMachines

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (n : ℕ) (hn : 0 < n)
    (i : Fin d) (x : K) :
    (coordinatePolynomial b n i (x^n)).eval (b.equivFun x i) = 0 :=
  coordinatePolynomial_root b n hn i x

-- Input zero and arbitrary signs require no exceptional branch.
example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (i : Fin d) :
    (coordinatePolynomial b 2 i 0).eval 0 = 0 := by
  simpa using coordinatePolynomial_root b 2 (by decide) i 0

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (i : Fin d) (x : K) :
    (coordinatePolynomial b 2 i ((-x)^2)).eval (b.equivFun (-x) i) = 0 :=
  coordinatePolynomial_root b 2 (by decide) i (-x)

-- Exponent zero is allowed for coefficient construction, not root correctness.
example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (i : Fin d) (y : K) :
    (coordinatePolynomial b 0 i y).Monic := coordinatePolynomial_monic b 0 i y

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (n : ℕ) (i : Fin d) :
    FP (numberFieldEncoding b) (BitEncoding.rat.vector ((n*d)^d+1))
      (coefficients b n i) := fp_coefficients b n i

example {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ K) (n : ℕ) (hn : 0 < n)
    (i : Fin d) (x : K) :
    ∑ k : Fin ((n*d)^d+1), coefficients b n i (x^n) k * b.equivFun x i ^ k.val = 0 :=
  coefficients_root b n hn i x
