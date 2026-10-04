import PlanarHom.BooleanFieldTowerProjectorMachines
import PlanarHom.GroupedProductInterpolation

/-! Exact polynomial semantics of the runtime grouped-projector program. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerProjectorSemantics
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
open BooleanFieldTowerProjectorMachines GroupedProjectorValueMachines
variable {K : Type} [Field K] [Algebra ℚ K]

theorem listProduct_eq (n : ℕ) (ds : List K) (xs : List (Carrier (radicands ds) n)) :
    listProduct (operations n) (ds,xs) = xs.prod := by
  change xs.foldl (mul (radicands ds) n) (embed n 1) = _
  rw [← one_eq (radicands ds) n, BooleanFieldTowerProductMachines.fold_mul_eq, one_mul]

theorem term_eq (n : ℕ) (ds : List K) (z b : Carrier (radicands ds) n)
    (xs : List (Carrier (radicands ds) n)) (j : ℕ) :
    term (operations n) (ds,((z,b),(xs,j))) = LinearProductDividedDifference.term z b xs j := by
  unfold term
  rw [listProduct_eq]
  unfold LinearProductDividedDifference.term
  simp only [factor, operations, sub_eq, one_eq]
  rfl

theorem dividedValue_eq (n : ℕ) (ds : List K) (z b : Carrier (radicands ds) n)
    (xs : List (Carrier (radicands ds) n)) :
    dividedValue (operations n) (ds,((z,b),xs)) =
      (LinearProductDividedDifference.polynomial xs /ₘ (Polynomial.X-Polynomial.C b)).eval z := by
  rw [← LinearProductDividedDifference.value_eq]
  unfold dividedValue LinearProductDividedDifference.value
  simp only [term_eq]
  change BooleanFieldTowerSumMachines.sum n _ = _
  exact (sum_eq (radicands ds) n _).symm

theorem rootValue_eq (n : ℕ) (ds : List K) (z : Carrier (radicands ds) n)
    (xs : List (Carrier (radicands ds) n)) :
    rootValue (operations n) (ds,(z,xs)) = (LinearProductDividedDifference.polynomial xs).eval z := by
  unfold rootValue
  rw [listProduct_eq, LinearProductDividedDifference.polynomial_eval]
  simp only [operations, sub_eq]
  rfl

theorem inverse_eq (D : ℕ → K) (n : ℕ) (p : Carrier D n) (h : norm D n p ≠ 0) :
    BooleanFieldTowerInverse.inverse D n p = Ring.inverse p := by
  exact (Ring.inverse_unit (BooleanFieldTowerInverse.unit D n p h)).symm

theorem reciprocalValue_eq (n : ℕ) (ds : List K) (z b : Carrier (radicands ds) n)
    (xs : List (Carrier (radicands ds) n))
    (h : norm (radicands ds) n (Polynomial.eval (R := Carrier (radicands ds) n) b (LinearProductDividedDifference.polynomial xs)) ≠ 0) :
    reciprocalValue (operations n) (ds,(z,(xs,b))) =
      (GroupedProductInterpolation.reciprocalFactor (LinearProductDividedDifference.polynomial xs) b).eval z := by
  unfold reciprocalValue
  rw [rootValue_eq, dividedValue_eq]
  simp only [operations, GroupedProductInterpolation.reciprocalFactor, Polynomial.eval_mul,
    Polynomial.eval_C, mul_eq, neg_eq]
  rw [inverse_eq _ _ _ h]

/-- Exact represented polynomial computed at z. Only outsider evaluations
of the group polynomial must have nonzero algebra norm. -/
theorem projectorValue_eq (n : ℕ) (ds : List K) (z : Carrier (radicands ds) n)
    (inside outside : List (Carrier (radicands ds) n))
    (h : ∀ b ∈ outside, norm (radicands ds) n
      (Polynomial.eval (R := Carrier (radicands ds) n) b (LinearProductDividedDifference.polynomial inside)) ≠ 0) :
    projectorValue (operations n) (ds,(z,(inside,outside))) =
      (LinearProductDividedDifference.polynomial outside *
        (outside.map (GroupedProductInterpolation.reciprocalFactor
          (LinearProductDividedDifference.polynomial inside))).prod).eval z := by
  unfold projectorValue
  rw [rootValue_eq, listProduct_eq]
  simp only [operations, Polynomial.eval_mul, Polynomial.eval_list_prod, List.map_map, Function.comp_def,
    mul_eq]
  congr 1
  congr 1
  apply List.map_congr_left
  intro b hb
  exact reciprocalValue_eq n ds z b inside (h b hb)

end PlanarHom.BooleanFieldTowerProjectorSemantics
