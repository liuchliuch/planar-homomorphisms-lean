import PlanarHom.LagrangeRecoveryMachines
import PlanarHom.LagrangeRecovery
import PlanarHom.RepresentativeWordCertificates

/-! Alignment of the actual row-list recovery program with shifted Lagrange interpolation. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.LagrangeRecoveryListSemantics
open Polynomial LagrangeRecovery LagrangeRecoveryMachines LagrangeCoefficientMachines
variable {K I : Type} [Field K] [DecidableEq K] {n : ℕ}

/-- Finite vector zip and the literal shortest-list operation agree at equal lengths. -/
theorem zipWith_ofFn {A B D : Type} (f : A → B → D) (a : Fin n → A) (b : Fin n → B) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipWith, List.getElem_ofFn]

/-- Removing one distinct source node leaves precisely the other indexed factors. -/
theorem filtered_product {S : Type} [CommMonoid S] (μ : Fin n → K)
    (hμ : Function.Injective μ) (j : Fin n) (f : K → S) :
    (((List.ofFn μ).filter (fun x => decide (x ≠ μ j))).map f).prod =
      ∏ i ∈ Finset.univ.erase j, f (μ i) := by
  have hp := List.prod_map_ite (fun x => x ≠ μ j) f (fun _ => (1 : S)) (List.ofFn μ)
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at hp
  rw [← hp, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ne_eq, hμ.eq_iff]
  rw [← Finset.prod_filter, Finset.filter_ne']

theorem filtered_length (μ : Fin n → K) (hμ : Function.Injective μ) (j : Fin n) :
    ((List.ofFn μ).filter (fun x => decide (x ≠ μ j))).length + 1 = n := by
  have hn := List.nodup_ofFn.mpr hμ
  have hf : (fun x : K => decide (x ≠ μ j)) = (fun x => x != μ j) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hf, ← hn.erase_eq_filter, List.length_erase_of_mem (List.mem_ofFn.mpr ⟨j,rfl⟩),
    List.length_ofFn]
  have hj := j.isLt
  omega

/-- The actual coefficient construction emits exactly n ascending numerator coefficients. -/
theorem filtered_coefficients (μ : Fin n → K) (hμ : Function.Injective μ) (j : Fin n) :
    productCoefficients ((List.ofFn μ).filter (fun x => decide (x ≠ μ j))) =
      List.ofFn (fun h : Fin n => (numerator μ j).coeff h.val) := by
  rw [productCoefficients_ofFn, filtered_length μ hμ j]
  rw [filtered_product μ hμ j (fun x => X - C x)]
  rfl

/-- This statement compares the actual compiled recovery function, not a replacement algorithm. -/
theorem recover_eq_evaluateReplacement (A : I → K) (input : LagrangeRecoveryMachines.Input A)
    (μ η y : Fin n → K) (hμ : Function.Injective μ)
    (htable : input.val.2.1 = List.ofFn (fun i => (μ i, η i)))
    (hanswers : input.val.2.2 = List.ofFn y) :
    recover A input = evaluateReplacement μ η y := by
  unfold recover evaluateReplacement
  rw [htable, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, rowTerm, otherNodes, htable, hanswers,
    List.map_ofFn, Function.comp_def]
  rw [filtered_coefficients μ hμ j, zipWith_ofFn, List.sum_ofFn]
  have hd : MaterializedFieldListMachines.shiftedDenominator
      (μ j, (List.ofFn μ).filter (fun x => decide (x ≠ μ j))) = denominator μ j := by
    simp only [MaterializedFieldListMachines.shiftedDenominator]
    rw [filtered_product μ hμ j (fun x => μ j - x)]
    rfl
  rw [hd, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [recoveryPolynomial, Polynomial.coeff_C_mul, div_eq_mul_inv]
  ring

/-- A literal input to the compiled recovery machine, backed by the actual representative table. -/
def computedInput {t : ℕ} (A B : Fin t → K) (m : ℕ) (answers : List K) : LagrangeRecoveryMachines.Input A :=
  ⟨(m,(ExponentProductTables.representatives A B m, answers)),
    ExponentProductTables.source_nodes_valid A B m⟩

/-- Actual computed rows and answer order agree exactly with the proved interpolation expression. -/
theorem recover_computed_table {t : ℕ} (A B : Fin t → K) (m : ℕ)
    (y : Fin (ExponentProductTables.representatives A B m).length → K) :
    recover A (computedInput A B m (List.ofFn y)) =
      evaluateReplacement (ExponentProductTables.sourceNode A B m)
        (ExponentProductTables.targetNode A B m) y := by
  apply recover_eq_evaluateReplacement A _ _ _ y (ExponentProductTables.sourceNode_injective A B m) _ rfl
  change ExponentProductTables.representatives A B m = _
  simpa only [ExponentProductTables.sourceNode, ExponentProductTables.targetNode, Prod.eta] using
    (List.ofFn_get (ExponentProductTables.representatives A B m)).symm

end PlanarHom.LagrangeRecoveryListSemantics
