import PlanarHom.BooleanGroupedRecoveryBounds
import PlanarHom.BooleanGroupedTableRecoverySemantics
import PlanarHom.BooleanFieldTowerPolynomialMachines

open PlanarHom

example : MaterializedGridWeightsMachines.grid (K := ℚ) 2 = [0,1,2] := by
  norm_num [MaterializedGridWeightsMachines.grid, List.range_succ]

example : MaterializedGridWeightsMachines.weights (([0,1,2] : List ℚ),[0,3,3]) = [-3,3,0] := by
  norm_num [MaterializedGridWeightsMachines.weights, MaterializedGridWeightsMachines.weight,
    MaterializedGridWeightsMachines.others, LagrangeCoefficientMachines.productCoefficients,
    LinearFactorCoefficientMachines.mulLinear, LinearFactorCoefficientMachines.go]

example : GroupedProjectorValueMachines.projectorValue
    (BooleanFieldTowerProjectorMachines.operations (K := ℚ) 0) ([],(1,([1,1],[0]))) = 1 := by
  norm_num [GroupedProjectorValueMachines.projectorValue, GroupedProjectorValueMachines.rootValue,
    GroupedProjectorValueMachines.listProduct, GroupedProjectorValueMachines.reciprocalValue,
    GroupedProjectorValueMachines.dividedValue, GroupedProjectorValueMachines.term,
    GroupedProjectorValueMachines.factor, BooleanFieldTowerProjectorMachines.operations,
    BooleanFieldTowerInverse.inverse, BooleanFieldTowerSumMachines.sum, BooleanFieldTower.mul,
    BooleanFieldTower.sub, BooleanFieldTower.neg, BooleanFieldTower.add, BooleanFieldTower.zero,
    BooleanFieldTower.embed]

example : BooleanGroupedGridRecoveryMachines.recover (K := ℚ) 0
    ([],(2,([(7,([1,1],[0]))],[0,3,3]))) = 21 := by
  norm_num [BooleanGroupedGridRecoveryMachines.recover,
    BooleanFieldTowerInverse.constantCoeff, BooleanGroupedGridRecoveryMachines.recoverTower,
    BooleanGroupedGridRecoveryMachines.gridValues, BooleanGroupedGridRecoveryMachines.weightedValue,
    BooleanGroupedGridRecoveryMachines.weightedRow,
    MaterializedGridWeightsMachines.grid, MaterializedGridWeightsMachines.weights,
    MaterializedGridWeightsMachines.weight, MaterializedGridWeightsMachines.others,
    LagrangeCoefficientMachines.productCoefficients, LinearFactorCoefficientMachines.mulLinear,
    LinearFactorCoefficientMachines.go, BooleanFieldTowerRecoveryMachines.dot,
    RuntimeDotProductMachines.dot, GroupedProjectorValueMachines.projectorValue,
    GroupedProjectorValueMachines.rootValue, GroupedProjectorValueMachines.listProduct,
    GroupedProjectorValueMachines.reciprocalValue, GroupedProjectorValueMachines.dividedValue,
    GroupedProjectorValueMachines.term, GroupedProjectorValueMachines.factor,
    BooleanFieldTowerProjectorMachines.operations, BooleanFieldTowerInverse.inverse,
    BooleanFieldTowerSumMachines.sum, BooleanFieldTower.mul, BooleanFieldTower.sub,
    BooleanFieldTower.neg, BooleanFieldTower.add, BooleanFieldTower.zero, BooleanFieldTower.embed,
    List.range_succ]

#check BooleanGroupedTableRecoveryMachines.fp_recover
#check BooleanGroupedRecoveryBounds.intermediate_encoding_bounds
#check BooleanFieldTowerPolynomialMachines.fp_evaluate
#check BooleanFieldTowerPolynomialMachines.fp_quotientCoefficients
#check BooleanFieldTowerProjectorSemantics.projectorValue_eq

#check BooleanGroupedGridRecoverySemantics.recoverTower_eq_coefficient_functional
#check BooleanGroupedTableRecoverySemantics.tablePolynomial_degree
#check BooleanGroupedTableRecoverySemantics.tablePolynomial_zero
#check BooleanGroupedTableRecoverySemantics.recoverTower_eq_positive_functional
