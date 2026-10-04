import PlanarHom.MaterializedLagrangeRecoveryMachines
import PlanarHom.MixedEvaluationFieldMap
import PlanarHom.SourceInterpolationWeights

/-! Source interpolation is performed wholly in K; only the recovered scalar
weights are embedded into the target field. Target multipliers need not belong
to K, and no compositum of parameter fields is used. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.CrossFieldInterpolationSemantics
open LagrangeRecovery Interpolation
variable {K L : Type} [Field K] [Field L] {n : ℕ}

def rowWeight (μ y : Fin n → K) (j : Fin n) : K :=
  ∑ h : Fin n, (recoveryPolynomial μ j).coeff h.val * y h

@[simp] theorem map_recoveryPolynomial (φ : K →+* L) (μ : Fin n → K) (j : Fin n) :
    (recoveryPolynomial μ j).map φ = recoveryPolynomial (fun i => φ (μ i)) j := by
  simp [recoveryPolynomial, numerator, denominator, Polynomial.map_prod]

@[simp] theorem map_rowWeight (φ : K →+* L) (μ y : Fin n → K) (j : Fin n) :
    φ (rowWeight μ y j) = rowWeight (fun i => φ (μ i)) (fun i => φ (y i)) j := by
  simp only [rowWeight, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Polynomial.coeff_map, map_recoveryPolynomial]

/-- Every individual fixed-K interpolation coefficient is recovered exactly. -/
theorem rowWeight_queryValues (μ a : Fin n → K) (hμ : Function.Injective μ)
    (hzero : ∀ i, μ i ≠ 0) (j : Fin n) : rowWeight μ (queryValues μ a) j = a j :=
  recover_one μ a hμ hzero j

/-- Only the target multipliers vary over L; all source queries and recovered
class weights remain in K with their original output representation. -/
theorem crossField_queryValues (φ : K →+* L) (μ a : Fin n → K) (η : Fin n → L)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    (∑ j, φ (rowWeight μ (queryValues μ a) j) * η j) = ∑ j, φ (a j) * η j := by
  simp only [rowWeight_queryValues μ a hμ hzero]

/-- The heterogeneous-field recovery identity retains every signed unchanged
assignment factor and each original target monomial. -/
theorem crossField_grouped_queries {S : Type} [Fintype S]
    (φ : K →+* L) (classOf : S → Fin n) (rest : S → K) (μ : Fin n → K) (η : Fin n → L)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    (∑ j, φ (rowWeight μ (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val+1)) j) * η j) =
      ∑ a, φ (rest a) * η (classOf a) := by
  have hy : (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val+1)) =
      queryValues μ (classCoefficients classOf rest) := funext (grouped_queryValues classOf rest μ)
  rw [hy, crossField_queryValues φ μ _ η hμ hzero]
  have hm (j) : φ (classCoefficients classOf rest j) =
      classCoefficients classOf (fun a => φ (rest a)) j := by
    simp [classCoefficients, map_sum]
  simp_rw [hm, mul_comm]
  exact sum_classCoefficients classOf (fun a => φ (rest a)) η

variable [DecidableEq K]

/-- The literal source-field row program equals the finite Lagrange row weight. -/
theorem weight_ofFn (μ y : Fin n → K) (xs : Fin n → List ℕ)
    (hμ : Function.Injective μ) (j : Fin n) :
    SourceInterpolationWeights.weight (List.ofFn (fun i => (μ i, xs i))) (List.ofFn y) (μ j) =
      rowWeight μ y j := by
  unfold SourceInterpolationWeights.weight SourceInterpolationWeights.table
    MaterializedLagrangeRecoveryMachines.rowTerm MaterializedLagrangeRecoveryMachines.otherNodes
  simp only [List.map_ofFn, Function.comp_def]
  rw [LagrangeRecoveryListSemantics.filtered_coefficients μ hμ j,
    LagrangeRecoveryListSemantics.zipWith_ofFn, List.sum_ofFn]
  have hd : MaterializedFieldListMachines.shiftedDenominator
      (μ j, (List.ofFn μ).filter (fun x => decide (x ≠ μ j))) = denominator μ j := by
    simp only [MaterializedFieldListMachines.shiftedDenominator]
    rw [LagrangeRecoveryListSemantics.filtered_product μ hμ j (fun x => μ j - x)]
    rfl
  rw [hd, Finset.mul_sum]
  unfold rowWeight
  apply Finset.sum_congr rfl
  intro h _
  simp only [recoveryPolynomial, Polynomial.coeff_C_mul, one_div]
  ring

theorem weightedRows_ofFn (μ y : Fin n → K) (xs : Fin n → List ℕ)
    (hμ : Function.Injective μ) :
    SourceInterpolationWeights.weightedRows (List.ofFn (fun i => (μ i, xs i))) (List.ofFn y) =
      List.ofFn (fun i => (rowWeight μ y i, xs i)) := by
  simp only [SourceInterpolationWeights.weightedRows, List.map_ofFn, Function.comp_def,
    weight_ofFn μ y xs hμ]

/-- The actual target aggregation consumes the retained exponent payloads. -/
def aggregate {t : ℕ} (φ : K →+* L) (B : Fin t → L)
    (rows : List (K × List ℕ)) (answers : List K) : L :=
  ((SourceInterpolationWeights.weightedRows rows answers).map
    (fun row => φ row.1 * ExponentProductSemantics.value B row.2)).sum

theorem aggregate_ofFn {t : ℕ} (φ : K →+* L) (B : Fin t → L)
    (μ y : Fin n → K) (xs : Fin n → List ℕ) (hμ : Function.Injective μ) :
    aggregate φ B (List.ofFn (fun i => (μ i, xs i))) (List.ofFn y) =
      ∑ j, φ (rowWeight μ y j) * ExponentProductSemantics.value B (xs j) := by
  rw [aggregate, weightedRows_ofFn μ y xs hμ, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Complete cross-field list recovery for grouped actual assignments. -/
theorem aggregate_grouped_queries {S : Type} [Fintype S] {t : ℕ}
    (φ : K →+* L) (B : Fin t → L) (classOf : S → Fin n) (rest : S → K)
    (μ : Fin n → K) (xs : Fin n → List ℕ)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    aggregate φ B (List.ofFn (fun i => (μ i, xs i)))
      (List.ofFn (fun h : Fin n => ∑ a, rest a * μ (classOf a) ^ (h.val+1))) =
      ∑ a, φ (rest a) * ExponentProductSemantics.value B (xs (classOf a)) := by
  rw [aggregate_ofFn φ B μ _ xs hμ]
  exact crossField_grouped_queries φ classOf rest μ
    (fun i => ExponentProductSemantics.value B (xs i)) hμ hzero

end PlanarHom.CrossFieldInterpolationSemantics
