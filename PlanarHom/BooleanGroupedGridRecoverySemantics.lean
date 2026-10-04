import PlanarHom.BooleanGroupedGridRecoveryMachines
import PlanarHom.MaterializedGridWeightsSemantics
import Mathlib.Algebra.CharP.Algebra

/-! Exact coefficient-functional semantics of the complete grouped grid circuit.
Only the scalar K is a field; the represented radical algebra is a CommRing. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanGroupedGridRecoverySemantics
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
open BooleanFieldTowerProjectorSemantics BooleanGroupedGridRecoveryMachines
variable {K : Type} [Field K] [Algebra ℚ K]

def rowPolynomial (n : ℕ) (ds : List K) (r : Row K n) :
    Polynomial (Carrier (radicands ds) n) :=
  Polynomial.C (ofTower (radicands ds) n r.1) *
    (LinearProductDividedDifference.polynomial (R := Carrier (radicands ds) n) r.2.2 *
      (r.2.2.map (fun b : Carrier (radicands ds) n => GroupedProductInterpolation.reciprocalFactor
        (LinearProductDividedDifference.polynomial (R := Carrier (radicands ds) n) r.2.1) b)).prod)

def rowsPolynomial (n : ℕ) (ds : List K) (rows : List (Row K n)) :
    Polynomial (Carrier (radicands ds) n) := (rows.map (rowPolynomial n ds)).sum

/-- Exactly the denominator promise used by the executable inverse calls. -/
def RowValid (n : ℕ) (ds : List K) (r : Row K n) : Prop :=
  ∀ b ∈ r.2.2, norm (radicands ds) n (Polynomial.eval (R := Carrier (radicands ds) n) b
    (LinearProductDividedDifference.polynomial (R := Carrier (radicands ds) n) r.2.1)) ≠ 0

theorem weightedRow_eq (n : ℕ) (ds : List K) (z : Carrier (radicands ds) n) (r : Row K n)
    (h : RowValid n ds r) : weightedRow n ((ds,z),r) = (rowPolynomial n ds r).eval z := by
  unfold weightedRow
  rw [projectorValue_eq n ds z r.2.1 r.2.2 h]
  simp only [rowPolynomial, Polynomial.eval_mul, Polynomial.eval_C, mul_eq, ofTower]

theorem weightedValue_eq (n : ℕ) (ds : List K) (z : Carrier (radicands ds) n)
    (rows : List (Row K n)) (h : ∀ r ∈ rows, RowValid n ds r) :
    weightedValue n (ds,(z,rows)) = (rowsPolynomial n ds rows).eval z := by
  unfold weightedValue rowsPolynomial
  change _ = (Polynomial.evalRingHom z) _
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  rw [sum_eq]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact weightedRow_eq n ds z r (h r hr)

theorem gridValues_eq_ofFn (n : ℕ) (ds : List K) (d : ℕ) (rows : List (Row K n))
    (h : ∀ r ∈ rows, RowValid n ds r) :
    gridValues n (ds,(d,rows)) = List.ofFn (fun j : Fin (d+1) =>
      (rowsPolynomial n ds rows).eval (algebraMap K (Carrier (radicands ds) n) (j.val : K))) := by
  unfold gridValues
  rw [MaterializedGridWeightsMachines.grid_eq_ofFn, List.map_ofFn]
  congr 1
  funext j
  exact weightedValue_eq n ds (ofTower (radicands ds) n (embed n (j.val : K))) rows h

/-- Actual recovered represented value equals the complete polynomial
coefficient-dot-moment functional. The bound is a degree fact, not a bit-cost
or coefficient-height hypothesis. -/
theorem recoverTower_eq_coefficient_functional (n : ℕ) (ds : List K) (d : ℕ)
    (rows : List (Row K n)) (y : Fin (d+1) → K)
    (hrows : ∀ r ∈ rows, RowValid n ds r)
    (hdegree : (rowsPolynomial n ds rows).natDegree ≤ d) :
    recoverTower n (ds,(d,(rows,List.ofFn y))) =
      ∑ r : Fin (d+1), (rowsPolynomial n ds rows).coeff r.val *
        algebraMap K (Carrier (radicands ds) n) (y r) := by
  letI : CharZero K := algebraRat.charZero K
  unfold recoverTower
  rw [BooleanFieldTowerRecoveryMachines.dot_eq, gridValues_eq_ofFn n ds d rows hrows]
  simp only [MaterializedGridWeightsMachines.weights, MaterializedGridWeightsMachines.grid_eq_ofFn,
    List.map_ofFn, LagrangeRecoveryListSemantics.zipWith_ofFn, List.sum_ofFn]
  simpa only [algebraMap_eq, MaterializedGridWeightsMachines.grid_eq_ofFn] using
    (MaterializedGridWeightsMachines.integer_coefficient_functional y
      (rowsPolynomial n ds rows) hdegree).symm

/-- Base-coordinate extraction is the final actual operation of the compiler. -/
theorem recover_eq_coefficient_functional (n : ℕ) (ds : List K) (d : ℕ)
    (rows : List (Row K n)) (y : Fin (d+1) → K)
    (hrows : ∀ r ∈ rows, RowValid n ds r)
    (hdegree : (rowsPolynomial n ds rows).natDegree ≤ d) :
    recover n (ds,(d,(rows,List.ofFn y))) = BooleanFieldTowerInverse.constantCoeff n
      (show Carrier (radicands ds) n from ∑ r : Fin (d+1), (rowsPolynomial n ds rows).coeff r.val *
        algebraMap K (Carrier (radicands ds) n) (y r)) := by
  unfold recover
  rw [recoverTower_eq_coefficient_functional n ds d rows y hrows hdegree]

end PlanarHom.BooleanGroupedGridRecoverySemantics
