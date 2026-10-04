import PlanarHom.MaterializedProductTableMachines
import PlanarHom.MaterializedLagrangeRecoveryMachines

open PlanarHom PlanarHom.Complexity
open PlanarHom.MaterializedProductTableMachines
open scoped BigOperators

example {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (BitEncoding.unaryNat.prod (numberFieldEncoding basis))
      (numberFieldEncoding basis) (fun p : ℕ × K => p.2 ^ p.1) :=
  MaterializedPowerMachines.fp_power basis

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension t : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (BitEncoding.unaryNat.prod
      (((numberFieldEncoding basis).vector t).prod ((numberFieldEncoding basis).vector t)))
      ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
      (fun p : ℕ × ((Fin t → K) × (Fin t → K)) =>
        ExponentProductTables.representatives p.2.1 p.2.2 p.1) := fp_representatives basis

example : MaterializedPowerMachines.powerStep^[0] ((0, 1) : ℚ × ℚ) = (0, 1) := rfl
example : MaterializedPowerMachines.powerStep^[5] ((-2, 3) : ℚ × ℚ) = (-2, -96) := by
  rw [MaterializedPowerMachines.powerStep_iterate]
  norm_num
example : MaterializedExponentProductMachines.product
    ((2, (![(2 : ℚ), 3]), ![5, 1]) : MaterializedExponentProductMachines.Input ℚ 2) = 12 := by
  norm_num [MaterializedExponentProductMachines.product, Fin.prod_univ_two]

-- Total zero-dimensional behavior and zero exponent.
example : products ((0, (Fin.elim0, Fin.elim0)) : Input ℚ 0) = [(1, 1)] := by
  change ExponentProductTables.products _ _ _ = _
  rw [ExponentProductTables.products_list_form]
  norm_num [ExponentVectors.weak, ExponentVectors.box, ExponentProductSemantics.value]
example : products ((1, (Fin.elim0, Fin.elim0)) : Input ℚ 0) = [] := by
  change ExponentProductTables.products _ _ _ = _
  rw [ExponentProductTables.products_list_form]
  norm_num [ExponentVectors.weak, ExponentVectors.box, ExponentProductSemantics.value]

-- Source collisions retain the earliest original target row.
example : representatives (t := 2) (K := ℚ) (1, ((fun _ => 2), ![3, 5])) = [(2, 3)] := by
  simp only [representatives, ExponentProductTables.representatives,
    ExponentProductTables.nonzeroProducts, ExponentProductTables.products_list_form]
  norm_num [ExponentVectors.weak, ExponentVectors.box, ExponentProductSemantics.value,
    Fin.prod_univ_two, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step]
  norm_num [List.range_succ, ListDedupMachines.step]
-- Nonzero filtering occurs before collision merging.
example : representatives (t := 2) (K := ℚ) (1, (![0, 2], ![3, 5])) = [(2, 5)] := by
  simp only [representatives, ExponentProductTables.representatives,
    ExponentProductTables.nonzeroProducts, ExponentProductTables.products_list_form]
  norm_num [ExponentVectors.weak, ExponentVectors.box, ExponentProductSemantics.value,
    Fin.prod_univ_two, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step]
  norm_num [List.range_succ, ListDedupMachines.step]
