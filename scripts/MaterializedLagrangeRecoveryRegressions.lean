import PlanarHom.MaterializedLagrangeRecoveryMachines

open PlanarHom PlanarHom.Complexity PlanarHom.LagrangeCoefficientMachines
open PlanarHom.LinearFactorCoefficientMachines
open PlanarHom.MaterializedLagrangeRecoveryMachines

-- Arbitrary input, without a source alphabet or promise subtype.
example {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (numberFieldEncoding basis).list (numberFieldEncoding basis).list
      (productCoefficients : List K → List K) :=
  MaterializedCoefficientMachines.fp_productCoefficients basis

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list.prod
      (numberFieldEncoding basis).list) (numberFieldEncoding basis) (recover : Data K → K) :=
  fp_recover basis

example : productCoefficients ([] : List ℚ) = [1] := rfl
example : productCoefficients ([2, 2] : List ℚ) = [4, -4, 1] := by
  norm_num [productCoefficients, mulLinear, go]
example : productCoefficients ([0, 3] : List ℚ) = [0, -3, 1] := by
  norm_num [productCoefficients, mulLinear, go]
example : recover (([], [1, 2]) : Data ℚ) = 0 := rfl
example : recover (([(0, 5)], [7]) : Data ℚ) = 0 := by
  norm_num [recover, rowTerm, otherNodes, productCoefficients, mulLinear, go,
    MaterializedFieldListMachines.shiftedDenominator]
example : recover (([(2, 4), (3, 9)], [5, 13]) : Data ℚ) = 13 := by
  norm_num [recover, rowTerm, otherNodes, productCoefficients, mulLinear, go,
    MaterializedFieldListMachines.shiftedDenominator]
-- The total fallback is also defined with duplicate nodes and mismatched answer length.
example : recover (([(2, 4), (2, 6)], [3, 100]) : Data ℚ) = 15 := by
  norm_num [recover, rowTerm, otherNodes, productCoefficients, mulLinear, go,
    MaterializedFieldListMachines.shiftedDenominator]
