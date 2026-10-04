import PlanarHom.MaterializedCoefficientMachines
import PlanarHom.LagrangeRecoveryListSemantics

/-! Total exact shifted-Lagrange table recovery on literal table and answer words. -/
namespace PlanarHom.MaterializedLagrangeRecoveryMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open LagrangeCoefficientMachines
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K]

abbrev Data (K : Type) := List (K × K) × List K

/-- Source-node filtering uses the original table order and actual field equality. -/
def otherNodes (μ : K) (table : List (K × K)) : List K :=
  (table.map Prod.fst).filter (fun ν => decide (ν ≠ μ))

/-- Total row calculation; inverse zero is the field's total inverse operation. -/
def rowTerm (input : Data K) (row : K × K) : K :=
  let others := otherNodes row.1 input.1
  let cs := productCoefficients others
  let den := MaterializedFieldListMachines.shiftedDenominator (row.1, others)
  (row.2 / den) * (List.zipWith (fun c y => c * y) cs input.2).sum

/-- Literal table recovery, with no alphabet, degree, distinctness or nonzero promise. -/
def recover (input : Data K) : K := (input.1.map (fun row => rowTerm input row)).sum

variable [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Preserve the exact ordinary framed table/list codecs. -/
noncomputable def inputEncoding : BitEncoding (Data K) :=
  ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list.prod
    (numberFieldEncoding basis).list

omit [DecidableEq K] in
theorem fp_table : FP (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list (fun input => input.1) :=
  fp_fst _ _

omit [DecidableEq K] in
theorem fp_answers : FP (inputEncoding basis) (numberFieldEncoding basis).list (fun input => input.2) :=
  fp_snd _ _

theorem fp_otherNodes : FP ((numberFieldEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list)
    (numberFieldEncoding basis).list (fun p => otherNodes p.1 p.2) :=
  LagrangeRecoveryMachines.fp_otherNodes basis

/-- Each row is an actual FP composition of filtering, linear-factor coefficient
updates, dynamic product, total division, and a shortest-list coefficient dot. -/
theorem fp_rowTerm : FP ((inputEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
    (numberFieldEncoding basis) (fun p => rowTerm p.1 p.2) := by
  have hc := fp_fst (inputEncoding basis) ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hr := fp_snd (inputEncoding basis) ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have ht := hc.comp (fp_table basis)
  have hy := hc.comp (fp_answers basis)
  have hμ := hr.comp (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  have hη := hr.comp (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))
  have ho := (hμ.pair ht).comp (fp_otherNodes basis)
  have hcs := ho.comp (MaterializedCoefficientMachines.fp_productCoefficients basis)
  have hd := (hμ.pair ho).comp (MaterializedFieldListMachines.fp_shiftedDenominator basis)
  have hscale := (hη.pair hd).comp (FixedFieldArithmetic.fp_division basis)
  have hdot := (hcs.pair hy).comp (FieldDotProductMachines.fp_dot basis)
  exact (hscale.pair hdot).comp (FixedFieldArithmetic.fp_multiplication basis)

/-- Total ordinary FP on exactly (table, answers), with all field words materialized. -/
theorem fp_recover : FP (inputEncoding basis) (numberFieldEncoding basis) (recover : Data K → K) := by
  have hrows := ListContextMachines.fp_mapWithContext (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) (numberFieldEncoding basis)
    (fun p => rowTerm p.1 p.2) (fp_rowTerm basis)
  exact ((((fp_id (inputEncoding basis)).pair (fp_table basis)).comp hrows).comp
    (MaterializedFieldListMachines.fp_sum basis))

omit [Algebra ℚ K] in
/-- The earlier promised function is the restriction of this same literal program. -/
theorem recover_restricted {I : Type} (A : I → K) (input : LagrangeRecoveryMachines.Input A) :
    recover input.val.2 = LagrangeRecoveryMachines.recover A input := rfl

omit [Algebra ℚ K] in
/-- Distinctness is used only here, to identify filtering with indexed Lagrange factors. -/
theorem recover_eq_evaluateReplacement {n : ℕ} (μ η y : Fin n → K)
    (hμ : Function.Injective μ) :
    recover (List.ofFn (fun i => (μ i, η i)), List.ofFn y) =
      LagrangeRecovery.evaluateReplacement μ η y := by
  unfold recover LagrangeRecovery.evaluateReplacement
  rw [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, rowTerm, otherNodes, List.map_ofFn, Function.comp_def]
  rw [LagrangeRecoveryListSemantics.filtered_coefficients μ hμ j,
    LagrangeRecoveryListSemantics.zipWith_ofFn, List.sum_ofFn]
  have hd : MaterializedFieldListMachines.shiftedDenominator
      (μ j, (List.ofFn μ).filter (fun x => decide (x ≠ μ j))) = LagrangeRecovery.denominator μ j := by
    simp only [MaterializedFieldListMachines.shiftedDenominator]
    rw [LagrangeRecoveryListSemantics.filtered_product μ hμ j (fun x => μ j - x)]
    rfl
  rw [hd, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [LagrangeRecovery.recoveryPolynomial, Polynomial.coeff_C_mul, div_eq_mul_inv]
  ring

omit [Algebra ℚ K] in
/-- Nonzero distinct nodes and the shifted query identity imply exact replacement. -/
theorem recover_queryValues {n : ℕ} (μ η a : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    recover (List.ofFn (fun i => (μ i, η i)), List.ofFn (Interpolation.queryValues μ a)) =
      ∑ i, η i * a i := by
  rw [recover_eq_evaluateReplacement μ η _ hμ]
  exact LagrangeRecovery.evaluateReplacement_queryValues μ η a hμ hzero

omit [Algebra ℚ K] in
/-- The same total machine recovers grouped assignment contributions. -/
theorem recover_grouped_queries {n : ℕ} {S : Type*} [Fintype S]
    (classOf : S → Fin n) (rest : S → K) (μ η : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    recover (List.ofFn (fun i => (μ i, η i)),
      List.ofFn (fun h : Fin n => ∑ a, rest a * μ (classOf a) ^ (h.val + 1))) =
      ∑ a, η (classOf a) * rest a := by
  rw [recover_eq_evaluateReplacement μ η _ hμ]
  exact LagrangeRecovery.evaluateReplacement_grouped_queries classOf rest μ η hμ hzero

omit [Algebra ℚ K] in
/-- Arbitrary materialized source/target tables from the existing exact representative
constructor feed the total computer directly, including when A varies with the input. -/
theorem recover_computed_table {t : ℕ} (A B : Fin t → K) (m : ℕ)
    (y : Fin (ExponentProductTables.representatives A B m).length → K) :
    recover (ExponentProductTables.representatives A B m, List.ofFn y) =
      LagrangeRecovery.evaluateReplacement (ExponentProductTables.sourceNode A B m)
        (ExponentProductTables.targetNode A B m) y := by
  exact LagrangeRecoveryListSemantics.recover_computed_table A B m y

end PlanarHom.MaterializedLagrangeRecoveryMachines
