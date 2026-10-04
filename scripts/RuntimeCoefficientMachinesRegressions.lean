import PlanarHom.RuntimePolynomialEvaluationMachines
import PlanarHom.RuntimeDotProductMachines

open PlanarHom
open CoefficientListAlgebra

example : evaluate (2 : ℚ) [3,4,5] = 31 := by norm_num [evaluate]
example : quotientCoefficients (1 : ℚ) [2,3,1] = [4,1,0] := by
  norm_num [quotientCoefficients]
example : convolution ([1,2] : List ℚ) [3,4] = [3,10,8,0,0] := by
  norm_num [convolution, convolutionCoefficient, List.range_succ]
example (b : ZMod 4) (cs : List (ZMod 4)) :
    polynomial (quotientCoefficients b cs) = polynomial cs /ₘ (Polynomial.X - Polynomial.C b) :=
  quotient_polynomial b cs
example (xs ys : List (ZMod 4)) : polynomial (convolution xs ys) = polynomial xs * polynomial ys :=
  convolution_polynomial xs ys

example : BooleanFieldTowerConvolutionMachines.convolution 1
    (([1] : List ℚ), ([(1,1)], [(1,-1)])) = [(0,0),(0,0),(0,0)] := by
  norm_num [BooleanFieldTowerConvolutionMachines.convolution,
    CoefficientConvolutionMachines.convolution, CoefficientConvolutionMachines.coefficient,
    CoefficientConvolutionMachines.term, BooleanFieldTowerSumMachines.sum,
    BooleanFieldTower.mul, BooleanFieldTower.add, BooleanFieldTower.zero,
    BooleanFieldTower.embed, BooleanFieldTowerConvolutionMachines.radicands, List.range_succ]

example (xs ys : List ℚ) :
    (xs.zipIdx.map (fun q => q.1 * ys[q.2]?.getD 0)).sum = (List.zipWith (· * ·) xs ys).sum :=
  RuntimeDotProductMachines.indexed_dot_eq xs ys

#check MaterializedPolynomialEvaluationMachines.fp_evaluate
#check SyntheticDivisionMachines.fp_quotientCoefficients
#check CoefficientConvolutionMachines.fp_fieldConvolution
#check BooleanFieldTowerConvolutionMachines.fp_convolution
#check BooleanFieldTowerRecoveryMachines.fp_dot
#check BooleanFieldTowerRecoveryMachines.fp_recoverConstant
#check RuntimePolynomialEvaluationMachines.fp_evaluate
