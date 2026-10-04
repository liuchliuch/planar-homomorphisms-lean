import PlanarHom.BooleanEffectiveLengthSamples

open PlanarHom.BooleanEffectiveSampling PlanarHom.BooleanEffectiveLengthSamples
open scoped BigOperators

-- The bound is materialized from the unary cap by a fixed polynomial.
example : (capPolynomial 1).eval 1=8 := by norm_num [capPolynomial]
example : PlanarHom.BooleanEffectiveSampling.prepare 1 (1,(2,[1])) = (10,(1,[1])) := by
  norm_num [PlanarHom.BooleanEffectiveSampling.prepare,capPolynomial]

-- Product length prepares the literal cap and class totals.
example : PlanarHom.BooleanEffectiveLengthSamples.prepare (fun _ : Fin 1 => 2) 2 3 =
    (6,(7,[6])) := by
  norm_num [PlanarHom.BooleanEffectiveLengthSamples.prepare,List.ofFn_succ]

-- Equal-diagonal classes are never incorrectly rejected for changing counts.
example (c w : Fin 1 → ℚ) (r : PlanarHom.BooleanNormSampleSearch.Row) :
    PlanarHom.BooleanNormSampleMachines.bad c (fun _ => 0) w r=false := by
  simp [PlanarHom.BooleanNormSampleMachines.bad,PlanarHom.BooleanNormSampleMachines.eligible]

-- The source-length endpoint compiles without a supplied tester, evaluator,
-- iteration bound, or candidate list.
example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension b : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (c a w : Fin b → K)
    (d : Fin b → ℕ) (ell : ℕ) :
    PlanarHom.Complexity.FP PlanarHom.Complexity.BitEncoding.unaryNat
      PlanarHom.Complexity.BitEncoding.rat.list (samples c a w d ell) :=
  fp_samples basis c a w d ell

-- The actual output, including m=0, has the required number of distinct samples.
example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b : ℕ}
    (f : K →+* ℝ) (c a w : Fin b → K) (d : Fin b → ℕ) (ell : ℕ)
    (hp : PlanarHom.BooleanExceptionalSource.SeparatedParameters
      (fun i => f (c i)) (fun i => f (a i)) (fun i => f (w i))) :
    1≤(samples c a w d ell 0).length ∧ (samples c a w d ell 0).Nodup := by
  exact ⟨by simpa using samples_length_ge f c a w d ell 0 hp,samples_nodup c a w d ell 0⟩
