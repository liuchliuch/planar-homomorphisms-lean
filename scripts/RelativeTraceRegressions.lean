import PlanarHom.RelativeTraceComputation
import PlanarHom.RankOneRealTractability

noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.RelativeTraceComputation
open PlanarHom.AlgebraicProductInterpolation

-- Relative trace divided by extension degree returns every actual base-field
-- value, independently for each finite extension.
example {K L : Type} [Field K] [Field L] [CharZero K]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [FiniteDimensional K L] (x : K) :
    Algebra.trace K L (algebraMap K L x)/(Module.finrank K L : K)=x := by
  rw [←descent_eq_trace_div_degree,descent_algebraMap]

example (x : ℚ) : descent (K:=ℚ) (L:=ℚ) x=x := by
  simpa using descent_algebraMap (K:=ℚ) (L:=ℚ) x

-- The answer converter is an actual FP machine, not a trace-evaluation oracle.
example {K L : Type} [Field K] [Field L] [CharZero K]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [FiniteDimensional K L] {d e : ℕ} (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) {α : Type} (ea : BitEncoding α) (f : α→K)
    (hf : FP ea (numberFieldEncoding bL) (fun x=>algebraMap K L (f x))) :
    FP ea (numberFieldEncoding bK) f := fp_base_value ea bK bL f hf

-- A rank-one real source may have amplitudes outside its original entry field.
-- Here M=[2] and w=[3], while the chosen amplitude is sqrt2. The endpoint
-- derives algebraicity and actually descends answers to the original basis.
private def sqrtSource : RealLanguage 1 1 0 where
  matrices := fun _ _ _=>2
  unaries := fun i=>Fin.elim0 i
  weights := fun _=>3
  matrices_algebraic := fun _ _ _=>isAlgebraic_nat 2
  unaries_algebraic := fun i=>Fin.elim0 i
  weights_algebraic := fun _=>isAlgebraic_nat 3

example : sqrtSource.problem.InFP := by
  apply sqrtSource.rankOne_inFP (fun _=>Real.sqrt 2)
  intro i j
  exact (Real.mul_self_sqrt (by norm_num : (0 : ℝ)≤2)).symm

#print axioms PlanarHom.RelativeTraceComputation.fp_descent
#print axioms PlanarHom.RelativeTraceComputation.fp_base_value
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.rankOne_inFP
