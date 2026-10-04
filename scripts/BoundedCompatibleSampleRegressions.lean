import PlanarHom.BoundedCompatibleSampleMachines

open PlanarHom PlanarHom.Complexity
open PlanarHom.MaterializedCollisionTestMachines

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension t : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (MaterializedProductTableMachines.inputEncoding basis t) BitEncoding.bool
      (test : MaterializedProductTableMachines.Input K t → Bool) := fp_test basis

example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension t : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (A : ℕ → Fin t → K)
    (hA : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t) A) :
    FP (BoundedCompatibleSampleMachines.inputEncoding basis t) BitEncoding.nat
      (BoundedCompatibleSampleMachines.search A) :=
  BoundedCompatibleSampleMachines.fp_search basis A hA

example : consistent ([(2, 3), (2, 5)] : List (ℚ × ℚ)) = false := by
  norm_num [consistent, badPair]
example : consistent ([(2, 3), (2, 3), (3, 8)] : List (ℚ × ℚ)) = true := by
  norm_num [consistent, badPair]
example : consistent ([(0, 3), (0, 5), (1, 7)] : List (ℚ × ℚ)) = true := by
  norm_num [consistent, badPair]

-- Test the exact semantic interface used by the current-length recovery proof.
example {K : Type} [Field K] [DecidableEq K] {t : ℕ} (m : ℕ) (A B : Fin t → K) :
    test (m, (A, B)) = true ↔ ExponentProductTables.CompatibleAt A B m :=
  test_eq_true_iff _

-- Empty candidate intervals use the stated total fallback.
example (A : ℕ → Fin 2 → ℚ) :
    BoundedCompatibleSampleMachines.search A (0, (1, ![3, 5])) = 0 := rfl

-- Candidate 2 fails, then candidate 1 is accepted in the actual descending order.
example : BoundedCompatibleSampleMachines.search
    (fun n => if n = 2 then ![(1 : ℚ), 1] else ![2, 3]) (3, (1, ![3, 5])) = 1 := by
  simp only [BoundedCompatibleSampleMachines.search, BoundedCompatibleSampleMachines.candidates,
    BoundedCompatibleSampleMachines.accept, test, MaterializedProductTableMachines.products,
    ExponentProductTables.products_list_form]
  norm_num [List.range_succ, ExponentVectors.weak, ExponentVectors.box,
    ExponentProductSemantics.value, Fin.prod_univ_two, consistent, badPair]
