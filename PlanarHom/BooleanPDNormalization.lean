import PlanarHom.CubeReindexTransport
import Mathlib.Data.Real.Sqrt

/-!
# Exact normalization of positive PD Boolean factors

This is the matrix-algebra normalization in equation (5.1). Every factor is
first put in a genuine color order, then normalized by the geometric mean of
its diagonal entries. The parameter inequalities and algebraicity are derived
from positive definiteness and the original entries.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.BooleanPDNormalization
open CubeTensorExponential MatrixCoordinateTransport

/-- The normalized two-color matrix in equation (5.1). -/
def normalForm (θ w : ℝ) : Matrix Bool Bool ℝ :=
  fun a b => if a = b then (if a then θ⁻¹ else θ) else w

/-- The scalar geometric mean of the two original diagonal entries. -/
def geometricScale (A : Matrix Bool Bool ℝ) : ℝ := Real.sqrt (A false false * A true true)

/-- The source's diagonal-ratio parameter. -/
def theta (A : Matrix Bool Bool ℝ) : ℝ := Real.sqrt (A false false / A true true)

/-- The normalized off-diagonal parameter. -/
def weight (A : Matrix Bool Bool ℝ) : ℝ := A false true / geometricScale A

/-- Positive definiteness gives the strict two-by-two determinant inequality. -/
theorem offDiagonal_sq_lt_diagonal_product (A : Matrix Bool Bool ℝ) (hA : A.PosDef) :
    A false true ^ 2 < A false false * A true true := by
  have hs : A true false = A false true := by
    simpa only [star_trivial] using hA.1.apply false true
  have hd := (reindex_posDef finTwoEquiv.symm hA).det_pos
  rw [Matrix.det_fin_two] at hd
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply, finTwoEquiv, hs, pow_two,
    sub_pos] using hd

/-- The normalizing scale is strictly positive. -/
theorem geometricScale_pos (A : Matrix Bool Bool ℝ) (hA : A.PosDef) : 0 < geometricScale A :=
  Real.sqrt_pos.mpr (mul_pos (posDef_diagonal_pos A hA false) (posDef_diagonal_pos A hA true))

/-- The weight parameter lies strictly between zero and one. -/
theorem weight_mem_Ioo (A : Matrix Bool Bool ℝ) (hA : A.PosDef) (hv : 0 < A false true) :
    0 < weight A ∧ weight A < 1 := by
  have hg := geometricScale_pos A hA
  have hsq : geometricScale A ^ 2 = A false false * A true true :=
    Real.sq_sqrt (mul_pos (posDef_diagonal_pos A hA false) (posDef_diagonal_pos A hA true)).le
  have hdet := offDiagonal_sq_lt_diagonal_product A hA
  refine ⟨div_pos hv hg, (div_lt_one hg).mpr ?_⟩
  nlinarith

/-- The ordered diagonal ratio is at least one. -/
theorem one_le_theta (A : Matrix Bool Bool ℝ) (hA : A.PosDef)
    (horder : A true true ≤ A false false) : 1 ≤ theta A := by
  exact Real.one_le_sqrt.mpr ((one_le_div (posDef_diagonal_pos A hA true)).mpr horder)

/-- The diagonal ratio is strictly positive before any color ordering. -/
theorem theta_pos (A : Matrix Bool Bool ℝ) (hA : A.PosDef) : 0 < theta A :=
  Real.sqrt_pos.mpr (div_pos (posDef_diagonal_pos A hA false) (posDef_diagonal_pos A hA true))

/-- Unequal ordered diagonals are exactly the strict parameter case. -/
theorem theta_gt_one_iff (A : Matrix Bool Bool ℝ) (hA : A.PosDef)
    (horder : A true true ≤ A false false) :
    1 < theta A ↔ A false false ≠ A true true := by
  have ht := one_le_theta A hA horder
  have hθsq : theta A ^ 2 = A false false / A true true :=
    Real.sq_sqrt (div_pos (posDef_diagonal_pos A hA false) (posDef_diagonal_pos A hA true)).le
  have hz := posDef_diagonal_pos A hA true
  constructor
  · intro h hEq
    rw [hEq, div_self (ne_of_gt hz)] at hθsq
    nlinarith
  · intro hne
    have hlt : 1 < A false false / A true true :=
      (one_lt_div hz).mpr (lt_of_le_of_ne horder hne.symm)
    nlinarith

/-- Exact recovery of every matrix entry from the two parameters and scale. -/
theorem eq_scale_smul_normalForm (A : Matrix Bool Bool ℝ) (hA : A.PosDef) :
    A = geometricScale A • normalForm (theta A) (weight A) := by
  have hu := posDef_diagonal_pos A hA false
  have hz := posDef_diagonal_pos A hA true
  have hsu : Real.sqrt (A false false) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hsz : Real.sqrt (A true true) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hz)
  have hs : A true false = A false true := by
    simpa only [star_trivial] using hA.1.apply false true
  have hscale : geometricScale A = Real.sqrt (A false false) * Real.sqrt (A true true) :=
    Real.sqrt_mul hu.le _
  have htheta : theta A = Real.sqrt (A false false) / Real.sqrt (A true true) :=
    Real.sqrt_div hu.le _
  ext a b
  cases a <;> cases b
  · simp only [Matrix.smul_apply, normalForm, ite_true, Bool.false_eq_true, ite_false,
      smul_eq_mul, hscale, htheta]
    field_simp
    nlinarith [Real.sq_sqrt hu.le]
  · simp only [Matrix.smul_apply, normalForm, Bool.false_eq_true, ite_false,
      smul_eq_mul, weight]
    exact (mul_div_cancel₀ _ (ne_of_gt (geometricScale_pos A hA))).symm
  · simp only [Matrix.smul_apply, normalForm, Bool.true_eq_false, ite_false,
      smul_eq_mul, weight, hs]
    exact (mul_div_cancel₀ _ (ne_of_gt (geometricScale_pos A hA))).symm
  · simp only [Matrix.smul_apply, normalForm, ite_true, smul_eq_mul, hscale, htheta,
      inv_div]
    field_simp
    nlinarith [Real.sq_sqrt hz.le]

/-- Algebraicity is closed under the actual nonnegative real square root. -/
theorem isAlgebraic_sqrt {x : ℝ} (hx : 0 ≤ x) (hAlg : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (Real.sqrt x) := by
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  simpa only [Real.sq_sqrt hx] using hAlg

/-- All three concrete parameters inherit algebraicity from the input matrix. -/
theorem parameters_isAlgebraic (A : Matrix Bool Bool ℝ) (hA : A.PosDef)
    (hAlg : ∀ a b, IsAlgebraic ℚ (A a b)) :
    IsAlgebraic ℚ (geometricScale A) ∧ IsAlgebraic ℚ (theta A) ∧
      IsAlgebraic ℚ (weight A) := by
  have hu := posDef_diagonal_pos A hA false
  have hz := posDef_diagonal_pos A hA true
  have hg : IsAlgebraic ℚ (geometricScale A) :=
    isAlgebraic_sqrt (mul_pos hu hz).le ((hAlg false false).mul (hAlg true true))
  refine ⟨hg, ?_, ?_⟩
  · apply isAlgebraic_sqrt (div_pos hu hz).le
    rw [div_eq_mul_inv]
    exact (hAlg false false).mul (hAlg true true).inv
  · exact (hAlg false true).mul hg.inv

/-- The actual color permutation which puts the larger diagonal first. -/
def colorOrder (A : Matrix Bool Bool ℝ) : Bool ≃ Bool :=
  if A true true ≤ A false false then Equiv.refl Bool else Equiv.swap false true

/-- Reindex both endpoints by the chosen color permutation. -/
def orderedFactor (A : Matrix Bool Bool ℝ) : Matrix Bool Bool ℝ :=
  Matrix.reindex (colorOrder A) (colorOrder A) A

/-- The permuted matrix really has its diagonals in the claimed order. -/
theorem orderedFactor_diagonal_order (A : Matrix Bool Bool ℝ) :
    orderedFactor A true true ≤ orderedFactor A false false := by
  by_cases h : A true true ≤ A false false
  · simpa [orderedFactor, colorOrder, h] using h
  · simpa [orderedFactor, colorOrder, h] using (le_of_not_ge h)

/-- Color exchange leaves the scalar geometric mean unchanged. -/
theorem geometricScale_orderedFactor (A : Matrix Bool Bool ℝ) :
    geometricScale (orderedFactor A) = geometricScale A := by
  by_cases h : A true true ≤ A false false
  · simp [orderedFactor, colorOrder, h]
  · simp [orderedFactor, colorOrder, h, geometricScale, mul_comm]

/-- The permutation preserves positive definiteness. -/
theorem orderedFactor_posDef (A : Matrix Bool Bool ℝ) (hA : A.PosDef) :
    (orderedFactor A).PosDef := reindex_posDef (colorOrder A) hA

/-- The permutation preserves all strict entry inequalities. -/
theorem orderedFactor_entry_pos (A : Matrix Bool Bool ℝ)
    (hpos : ∀ a b, 0 < A a b) (a b : Bool) : 0 < orderedFactor A a b :=
  hpos _ _

/-- Distinctness of the original diagonals is unaffected by the color order. -/
theorem orderedFactor_diagonal_ne_iff (A : Matrix Bool Bool ℝ) :
    orderedFactor A false false ≠ orderedFactor A true true ↔ A false false ≠ A true true := by
  by_cases h : A true true ≤ A false false
  · simp [orderedFactor, colorOrder, h]
  · simp [orderedFactor, colorOrder, h, ne_comm]

/-- The ordered parameter detects exactly the original unequal-diagonal case. -/
theorem ordered_theta_gt_one_iff (A : Matrix Bool Bool ℝ) (hA : A.PosDef) :
    1 < theta (orderedFactor A) ↔ A false false ≠ A true true := by
  rw [theta_gt_one_iff _ (orderedFactor_posDef A hA) (orderedFactor_diagonal_order A),
    orderedFactor_diagonal_ne_iff]

/-- Normalization leaves the local matrix positive definite. -/
theorem normalForm_posDef (A : Matrix Bool Bool ℝ) (hA : A.PosDef) :
    (normalForm (theta A) (weight A)).PosDef := by
  have h := hA.smul (inv_pos.mpr (geometricScale_pos A hA))
  have heq : (geometricScale A)⁻¹ • A = normalForm (theta A) (weight A) := calc
    (geometricScale A)⁻¹ • A =
        (geometricScale A)⁻¹ • (geometricScale A • normalForm (theta A) (weight A)) :=
      congrArg (fun X : Matrix Bool Bool ℝ => (geometricScale A)⁻¹ • X)
        (eq_scale_smul_normalForm A hA)
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (geometricScale_pos A hA)), one_smul]
  exact heq ▸ h

/-- Every entry of the normalized local matrix is strictly positive. -/
theorem normalForm_entry_pos (A : Matrix Bool Bool ℝ) (hA : A.PosDef)
    (hv : 0 < A false true) (a b : Bool) : 0 < normalForm (theta A) (weight A) a b := by
  have ht := theta_pos A hA
  have hw := (weight_mem_Ioo A hA hv).1
  cases a <;> cases b <;> simp [normalForm, ht, hw, inv_pos.mpr ht]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Simultaneously permute the two colors separately in every tensor factor. -/
def tensorColorOrder (F : ι → Matrix Bool Bool ℝ) : (ι → Bool) ≃ (ι → Bool) :=
  Equiv.piCongrRight (fun r => colorOrder (F r))

/-- The whole-matrix coordinate change is exactly the tensor of the local ones. -/
theorem reindex_tensor_order (F : ι → Matrix Bool Bool ℝ) :
    Matrix.reindex (tensorColorOrder F) (tensorColorOrder F) (tensor F) =
      tensor (fun r => orderedFactor (F r)) := by
  rfl

/-- The positive scalar in equation (5.1), for the ordered factors. -/
def tensorScale (F : ι → Matrix Bool Bool ℝ) : ℝ :=
  ∏ r, geometricScale (orderedFactor (F r))

/-- The scalar is the product of the original diagonal geometric means. -/
theorem tensorScale_eq_original (F : ι → Matrix Bool Bool ℝ) :
    tensorScale F = ∏ r, Real.sqrt (F r false false * F r true true) := by
  exact Finset.prod_congr rfl (fun r _ => geometricScale_orderedFactor (F r))

/-- The precise matrix-tensor identity after genuine coordinate permutations. -/
theorem reindex_tensor_eq_normalized (F : ι → Matrix Bool Bool ℝ)
    (hF : ∀ r, (F r).PosDef) :
    Matrix.reindex (tensorColorOrder F) (tensorColorOrder F) (tensor F) =
      tensorScale F • tensor (fun r =>
        normalForm (theta (orderedFactor (F r))) (weight (orderedFactor (F r)))) := by
  rw [reindex_tensor_order]
  have hterm : (fun r => orderedFactor (F r)) = fun r =>
      geometricScale (orderedFactor (F r)) •
        normalForm (theta (orderedFactor (F r))) (weight (orderedFactor (F r))) :=
    funext fun r => eq_scale_smul_normalForm _ (orderedFactor_posDef _ (hF r))
  rw [hterm, tensor_smul]
  rfl

/-- All source parameter inequalities follow simultaneously from the actual factors. -/
theorem normalized_tensor_parameters (F : ι → Matrix Bool Bool ℝ)
    (hF : ∀ r, (F r).PosDef) (hpos : ∀ r a b, 0 < F r a b) :
    0 < tensorScale F ∧ ∀ r,
      1 ≤ theta (orderedFactor (F r)) ∧
      0 < weight (orderedFactor (F r)) ∧ weight (orderedFactor (F r)) < 1 ∧
      (1 < theta (orderedFactor (F r)) ↔ F r false false ≠ F r true true) := by
  refine ⟨Finset.prod_pos (fun r _ => geometricScale_pos _ (orderedFactor_posDef _ (hF r))), ?_⟩
  intro r
  have hp := orderedFactor_posDef _ (hF r)
  have hw := weight_mem_Ioo _ hp (orderedFactor_entry_pos _ (hpos r) false true)
  exact ⟨one_le_theta _ hp (orderedFactor_diagonal_order _), hw.1, hw.2,
    ordered_theta_gt_one_iff _ (hF r)⟩

/-- Optional algebraicity is inherited by every scalar and local parameter. -/
theorem normalized_tensor_parameters_isAlgebraic (F : ι → Matrix Bool Bool ℝ)
    (hF : ∀ r, (F r).PosDef) (hAlg : ∀ r a b, IsAlgebraic ℚ (F r a b)) :
    IsAlgebraic ℚ (tensorScale F) ∧ ∀ r,
      IsAlgebraic ℚ (theta (orderedFactor (F r))) ∧
      IsAlgebraic ℚ (weight (orderedFactor (F r))) := by
  have hpar (r : ι) := parameters_isAlgebraic _ (orderedFactor_posDef _ (hF r))
    (fun a b => hAlg r ((colorOrder (F r)).symm a) ((colorOrder (F r)).symm b))
  refine ⟨?_, fun r => (hpar r).2⟩
  unfold tensorScale
  have hprod (s : Finset ι) : IsAlgebraic ℚ (∏ r ∈ s, geometricScale (orderedFactor (F r))) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))
    | @insert r s hr ih => simpa only [Finset.prod_insert hr] using (hpar r).1.mul ih
  exact hprod Finset.univ

/-- The normalized matrix entries themselves are algebraic, not only the parameters. -/
theorem normalForm_isAlgebraic (θ w : ℝ) (hθ : IsAlgebraic ℚ θ) (hw : IsAlgebraic ℚ w)
    (a b : Bool) : IsAlgebraic ℚ (normalForm θ w a b) := by
  cases a <;> cases b <;> simp only [normalForm, ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true]
  · exact hθ
  · exact hw
  · exact hw
  · exact hθ.inv

/-- Equation (5.1) with all inequalities and optional algebraicity, in one
statement whose color permutation and parameters are concrete constructions. -/
theorem normalized_tensor_spec (F : ι → Matrix Bool Bool ℝ)
    (hF : ∀ r, (F r).PosDef) (hpos : ∀ r a b, 0 < F r a b) :
    Matrix.reindex (tensorColorOrder F) (tensorColorOrder F) (tensor F) =
      tensorScale F • tensor (fun r =>
        normalForm (theta (orderedFactor (F r))) (weight (orderedFactor (F r)))) ∧
    0 < tensorScale F ∧
    (∀ r, 1 ≤ theta (orderedFactor (F r)) ∧
      0 < weight (orderedFactor (F r)) ∧ weight (orderedFactor (F r)) < 1 ∧
      (1 < theta (orderedFactor (F r)) ↔ F r false false ≠ F r true true)) ∧
    ((∀ r a b, IsAlgebraic ℚ (F r a b)) →
      IsAlgebraic ℚ (tensorScale F) ∧ ∀ r,
        IsAlgebraic ℚ (theta (orderedFactor (F r))) ∧
        IsAlgebraic ℚ (weight (orderedFactor (F r)))) := by
  obtain ⟨hg, hpar⟩ := normalized_tensor_parameters F hF hpos
  exact ⟨reindex_tensor_eq_normalized F hF, hg, hpar,
    normalized_tensor_parameters_isAlgebraic F hF⟩

end PlanarHom.BooleanPDNormalization
