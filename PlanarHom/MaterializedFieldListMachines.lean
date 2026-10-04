import PlanarHom.MaterializedFieldHeights
import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.ListContextMachines

/-! # Actual dynamic exact field sums, products, and shifted Lagrange denominators -/
namespace PlanarHom.MaterializedFieldListMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

omit [Algebra ℚ K] in
theorem fold_mul (a : K) (xs : List K) : xs.foldl (fun a x => a*x) a=a*xs.prod := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,mul_assoc]

omit [Algebra ℚ K] in
theorem fold_add (a : K) (xs : List K) : xs.foldl (fun a x => a+x) a=a+xs.sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]

theorem fp_fold_product : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (fun p : K×List K => p.1*p.2.prod) := by
  obtain ⟨p,hp⟩ := MaterializedFieldHeights.exists_polynomial_prefix_encoding_bound basis
  exact (ListFoldMachines.fp_foldl (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun a x => a*x) (FixedFieldArithmetic.fp_multiplication basis) p
    (fun a xs i _ => by simpa only [fold_mul] using (hp a xs i).1)).congr (fun p => fold_mul p.1 p.2)

theorem fp_fold_sum : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (fun p : K×List K => p.1+p.2.sum) := by
  obtain ⟨p,hp⟩ := MaterializedFieldHeights.exists_polynomial_prefix_encoding_bound basis
  exact (ListFoldMachines.fp_foldl (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun a x => a+x) (FixedFieldArithmetic.fp_addition basis) p
    (fun a xs i _ => by simpa only [fold_add] using (hp a xs i).2)).congr (fun p => fold_add p.1 p.2)

theorem fp_product : FP (numberFieldEncoding basis).list (numberFieldEncoding basis) (List.prod : List K→K) := by
  exact (((fp_const (numberFieldEncoding basis).list (numberFieldEncoding basis) 1).pair
    (fp_id (numberFieldEncoding basis).list)).comp (fp_fold_product basis)).congr (fun xs => by simp)

theorem fp_sum : FP (numberFieldEncoding basis).list (numberFieldEncoding basis) (List.sum : List K→K) := by
  exact (((fp_const (numberFieldEncoding basis).list (numberFieldEncoding basis) 0).pair
    (fp_id (numberFieldEncoding basis).list)).comp (fp_fold_sum basis)).congr (fun xs => by simp)

/-- The shifted denominator μ times the product of its differences from the
other nodes. This function is total, with no distinctness or nonzero promise. -/
def shiftedDenominator (p : K×List K) : K := p.1*(p.2.map (fun x => p.1-x)).prod

theorem fp_shiftedDenominator : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) shiftedDenominator := by
  have hm := fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis).list
  have hd := ListContextMachines.fp_mapWithContext (numberFieldEncoding basis) (numberFieldEncoding basis)
    (numberFieldEncoding basis) (fun p : K×K => p.1-p.2) (FixedFieldArithmetic.fp_subtraction basis)
  exact (hm.pair hd).comp (fp_fold_product basis)

/-- Scale an actual dynamic coefficient list by a materialized exact field value. -/
theorem fp_scale : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list (fun p : K×List K => p.2.map (fun x => p.1*x)) :=
  ListContextMachines.fp_mapWithContext _ _ _ _ (FixedFieldArithmetic.fp_multiplication basis)

end PlanarHom.MaterializedFieldListMachines
