import PlanarHom.Structures
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Monoid

/-!
# Fixed positive tensor charts are relatively closed

This file verifies the fixed-factorization, fixed-coordinate mechanism in
Lemma A.5. The tensor form is the actual Boolean Ising tensor, and its positive
parameters are recovered explicitly from matrix entries. No nondegeneracy
condition excludes parameters equal to one.

The finite union over all dimension factorizations and color permutations is
also verified, for both positive symmetric and positive rectangular blocks.
For everywhere-positive matrices the resulting theorem uses the original
`Structures.AllowedBlock` predicate.

Finally the full fixed-support statement for `Structures.NonnegativeClass`
is proved by a second finite union over all surjective direct-sum partitions.
This avoids requiring a separate uniqueness proof for connected support blocks.
The resulting closed-set and entrywise-limit statements are Lemma A.5 itself,
not only a fixed-chart proxy.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace PlanarHom.FixedChartClosedness

open Boolean

/-- Coordinates for a fixed positive block. -/
abbrev Colors (k d : ℕ) := Fin k × Cube d

/-- The relative domain of matrices whose every entry is strictly positive. -/
abbrev PositiveMatrix (I J : Type*) := {M : I → J → ℝ // ∀ i j, 0 < M i j}

/-- The positive symmetric tensor chart in these fixed coordinates. -/
def SymmetricForm {k d : ℕ} (M : Colors k d → Colors k d → ℝ) : Prop :=
  ∃ (a : Fin k → ℝ) (ρ : Fin d → ℝ),
    (∀ i, 0 < a i) ∧ (∀ r, 0 < ρ r) ∧
    ∀ u v, M u v = a u.1 * a v.1 * tensor ρ u.2 v.2

/-- A positive amplitude is recovered uniquely from its diagonal entry. -/
def symmetricAmplitude {k d : ℕ} (M : Colors k d → Colors k d → ℝ) (i : Fin k) : ℝ :=
  Real.sqrt (M (i, fun _ => false) (i, fun _ => false))

/-- Single-coordinate flips recover the Ising parameter. -/
def symmetricParameter {k d : ℕ} (i₀ : Fin k)
    (M : Colors k d → Colors k d → ℝ) (r : Fin d) : ℝ :=
  M (i₀, fun _ => false) (i₀, unitBit r) /
    M (i₀, fun _ => false) (i₀, fun _ => false)

lemma symmetricAmplitude_of_form {k d : ℕ} (a : Fin k → ℝ) (ρ : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (i : Fin k) :
    symmetricAmplitude (fun u v : Colors k d => a u.1 * a v.1 * tensor ρ u.2 v.2) i = a i := by
  simp only [symmetricAmplitude, tensor_diag, mul_one]
  exact Real.sqrt_mul_self (ha i).le

lemma symmetricParameter_of_form {k d : ℕ} (i₀ : Fin k)
    (a : Fin k → ℝ) (ρ : Fin d → ℝ) (ha : ∀ i, 0 < a i) (r : Fin d) :
    symmetricParameter i₀ (fun u v : Colors k d => a u.1 * a v.1 * tensor ρ u.2 v.2) r = ρ r := by
  simp only [symmetricParameter, tensor_unitBit, tensor_diag, mul_one]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (ne_of_gt (ha i₀)) (ne_of_gt (ha i₀)))

/-- Tensor membership is equivalent to finitely many identities involving
continuous, canonically recovered parameters on the positive domain. -/
theorem symmetricForm_iff_reconstruction {k d : ℕ} (i₀ : Fin k)
    (M : PositiveMatrix (Colors k d) (Colors k d)) :
    SymmetricForm M.val ↔ ∀ u v, M.val u v =
      symmetricAmplitude M.val u.1 * symmetricAmplitude M.val v.1 *
        tensor (symmetricParameter i₀ M.val) u.2 v.2 := by
  constructor
  · rintro ⟨a, ρ, ha, hρ, hM⟩
    have he : M.val = fun u v : Colors k d => a u.1 * a v.1 * tensor ρ u.2 v.2 := by
      funext u v
      exact hM u v
    rw [he]
    intro u v
    have hr : symmetricParameter i₀
        (fun u v : Colors k d => a u.1 * a v.1 * tensor ρ u.2 v.2) = ρ :=
      funext (symmetricParameter_of_form i₀ a ρ ha)
    rw [hr]
    simp only [symmetricAmplitude_of_form a ρ ha]
  · intro hM
    refine ⟨symmetricAmplitude M.val, symmetricParameter i₀ M.val, ?_, ?_, hM⟩
    · intro i
      exact Real.sqrt_pos.2 (M.property _ _)
    · intro r
      exact div_pos (M.property _ _) (M.property _ _)

lemma continuous_entry {I J : Type*} (i : I) (j : J) :
    Continuous (fun M : PositiveMatrix I J => M.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

lemma continuous_symmetricAmplitude {k d : ℕ} (i : Fin k) :
    Continuous (fun M : PositiveMatrix (Colors k d) (Colors k d) =>
      symmetricAmplitude M.val i) :=
  Real.continuous_sqrt.comp (continuous_entry _ _)

lemma continuous_symmetricParameter {k d : ℕ} (i₀ : Fin k) (r : Fin d) :
    Continuous (fun M : PositiveMatrix (Colors k d) (Colors k d) =>
      symmetricParameter i₀ M.val r) := by
  exact (continuous_entry _ _).div (continuous_entry _ _)
    (fun M => ne_of_gt (M.property _ _))

lemma continuous_tensor {X : Type*} [TopologicalSpace X] {d : ℕ}
    (ρ : X → Fin d → ℝ) (hρ : ∀ r, Continuous (fun x => ρ x r)) (u v : Cube d) :
    Continuous (fun x => tensor (ρ x) u v) := by
  unfold tensor
  apply continuous_finset_prod
  intro r hr
  by_cases huv : u r = v r
  · simpa only [W, huv, if_true] using (continuous_const : Continuous (fun _ : X => (1 : ℝ)))
  · simpa only [W, huv, if_false] using hρ r

/-- The fixed-coordinate positive symmetric tensor family is closed in the
space of positive matrices, with no restriction on Ising degeneracies. -/
theorem isClosed_symmetricForm {k d : ℕ} (i₀ : Fin k) :
    IsClosed {M : PositiveMatrix (Colors k d) (Colors k d) | SymmetricForm M.val} := by
  simp only [symmetricForm_iff_reconstruction i₀, Set.setOf_forall]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  exact isClosed_eq (continuous_entry u v)
    (((continuous_symmetricAmplitude u.1).mul (continuous_symmetricAmplitude v.1)).mul
      (continuous_tensor _ (continuous_symmetricParameter i₀) u.2 v.2))

/-- The positive rectangular tensor chart in independent fixed row/column coordinates. -/
def RectangularForm {k l d : ℕ} (M : Colors k d → Colors l d → ℝ) : Prop :=
  ∃ (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ),
    (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ (∀ r, 0 < ρ r) ∧
    ∀ u v, M u v = a u.1 * b v.1 * tensor ρ u.2 v.2

/-- A normalization of the row amplitudes requiring only division. -/
def rowAmplitude {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (M : Colors k d → Colors l d → ℝ) (i : Fin k) : ℝ :=
  M (i, fun _ => false) (j₀, fun _ => false) /
    M (i₀, fun _ => false) (j₀, fun _ => false)

/-- The matching normalization of the column amplitudes. -/
def columnAmplitude {k l d : ℕ} (i₀ : Fin k)
    (M : Colors k d → Colors l d → ℝ) (j : Fin l) : ℝ :=
  M (i₀, fun _ => false) (j, fun _ => false)

/-- The rectangular single-flip ratio. -/
def rectangularParameter {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (M : Colors k d → Colors l d → ℝ) (r : Fin d) : ℝ :=
  M (i₀, fun _ => false) (j₀, unitBit r) /
    M (i₀, fun _ => false) (j₀, fun _ => false)

lemma rectangularParameter_of_form {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (r : Fin d) :
    rectangularParameter i₀ j₀
      (fun (u : Colors k d) (v : Colors l d) => a u.1 * b v.1 * tensor ρ u.2 v.2) r = ρ r := by
  simp only [rectangularParameter, tensor_unitBit, tensor_diag, mul_one]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (ne_of_gt (ha i₀)) (ne_of_gt (hb j₀)))

lemma rectangularAmplitude_product_of_form {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (i : Fin k) (j : Fin l) :
    rowAmplitude i₀ j₀
        (fun (u : Colors k d) (v : Colors l d) => a u.1 * b v.1 * tensor ρ u.2 v.2) i *
      columnAmplitude i₀
        (fun (u : Colors k d) (v : Colors l d) => a u.1 * b v.1 * tensor ρ u.2 v.2) j =
      a i * b j := by
  simp only [rowAmplitude, columnAmplitude, tensor_diag, mul_one]
  field_simp [ne_of_gt (ha i₀), ne_of_gt (hb j₀)]

/-- Rectangular membership is equivalent to the canonical finite entry identities. -/
theorem rectangularForm_iff_reconstruction {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (M : PositiveMatrix (Colors k d) (Colors l d)) :
    RectangularForm M.val ↔ ∀ u v, M.val u v =
      rowAmplitude i₀ j₀ M.val u.1 * columnAmplitude i₀ M.val v.1 *
        tensor (rectangularParameter i₀ j₀ M.val) u.2 v.2 := by
  constructor
  · rintro ⟨a, b, ρ, ha, hb, hρ, hM⟩
    have he : M.val = fun (u : Colors k d) (v : Colors l d) =>
        a u.1 * b v.1 * tensor ρ u.2 v.2 := by
      funext u v
      exact hM u v
    rw [he]
    intro u v
    have hr : rectangularParameter i₀ j₀
        (fun (u : Colors k d) (v : Colors l d) => a u.1 * b v.1 * tensor ρ u.2 v.2) = ρ :=
      funext (rectangularParameter_of_form i₀ j₀ a b ρ ha hb)
    rw [hr, rectangularAmplitude_product_of_form i₀ j₀ a b ρ ha hb]
  · intro hM
    refine ⟨rowAmplitude i₀ j₀ M.val, columnAmplitude i₀ M.val,
      rectangularParameter i₀ j₀ M.val, ?_, ?_, ?_, hM⟩
    · intro i
      exact div_pos (M.property _ _) (M.property _ _)
    · intro j
      exact M.property _ _
    · intro r
      exact div_pos (M.property _ _) (M.property _ _)

lemma continuous_rowAmplitude {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l) (i : Fin k) :
    Continuous (fun M : PositiveMatrix (Colors k d) (Colors l d) =>
      rowAmplitude i₀ j₀ M.val i) := by
  exact (continuous_entry _ _).div (continuous_entry _ _)
    (fun M => ne_of_gt (M.property _ _))

lemma continuous_columnAmplitude {k l d : ℕ} (i₀ : Fin k) (j : Fin l) :
    Continuous (fun M : PositiveMatrix (Colors k d) (Colors l d) =>
      columnAmplitude i₀ M.val j) := continuous_entry _ _

lemma continuous_rectangularParameter {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l) (r : Fin d) :
    Continuous (fun M : PositiveMatrix (Colors k d) (Colors l d) =>
      rectangularParameter i₀ j₀ M.val r) := by
  exact (continuous_entry _ _).div (continuous_entry _ _)
    (fun M => ne_of_gt (M.property _ _))

/-- The fixed-coordinate positive rectangular tensor family is relatively closed. -/
theorem isClosed_rectangularForm {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l) :
    IsClosed {M : PositiveMatrix (Colors k d) (Colors l d) | RectangularForm M.val} := by
  simp only [rectangularForm_iff_reconstruction i₀ j₀, Set.setOf_forall]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  exact isClosed_eq (continuous_entry u v)
    (((continuous_rowAmplitude i₀ j₀ u.1).mul (continuous_columnAmplitude i₀ v.1)).mul
      (continuous_tensor _ (continuous_rectangularParameter i₀ j₀) u.2 v.2))

/-- Every member of the symmetric chart has strictly positive entries. -/
lemma SymmetricForm.positive {k d : ℕ} {M : Colors k d → Colors k d → ℝ}
    (hM : SymmetricForm M) : ∀ u v, 0 < M u v := by
  obtain ⟨a, ρ, ha, hρ, hM⟩ := hM
  intro u v
  rw [hM]
  exact mul_pos (mul_pos (ha _) (ha _)) (tensor_pos hρ _ _)

/-- Every member of the rectangular chart has strictly positive entries. -/
lemma RectangularForm.positive {k l d : ℕ} {M : Colors k d → Colors l d → ℝ}
    (hM : RectangularForm M) : ∀ u v, 0 < M u v := by
  obtain ⟨a, b, ρ, ha, hb, hρ, hM⟩ := hM
  intro u v
  rw [hM]
  exact mul_pos (mul_pos (ha _) (hb _)) (tensor_pos hρ _ _)

/-- Entrywise convergence to a positive limit preserves the symmetric chart.
The index may be any nontrivial filter, including sequences at infinity. -/
theorem symmetricForm_of_tendsto {k d : ℕ} (i₀ : Fin k)
    {A : Type*} {f : Filter A} [f.NeBot]
    (M : A → Colors k d → Colors k d → ℝ) (L : Colors k d → Colors k d → ℝ)
    (hM : ∀ n, SymmetricForm (M n)) (hL : ∀ u v, 0 < L u v)
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) : SymmetricForm L := by
  let P : A → PositiveMatrix (Colors k d) (Colors k d) :=
    fun n => ⟨M n, (hM n).positive⟩
  have hP : Tendsto P f (𝓝 (⟨L, hL⟩ : PositiveMatrix (Colors k d) (Colors k d))) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro u
    exact tendsto_pi_nhds.mpr (hlim u)
  exact (isClosed_symmetricForm i₀).mem_of_tendsto hP
    (Filter.Eventually.of_forall hM)

/-- Entrywise convergence to a positive limit preserves the rectangular chart. -/
theorem rectangularForm_of_tendsto {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    {A : Type*} {f : Filter A} [f.NeBot]
    (M : A → Colors k d → Colors l d → ℝ) (L : Colors k d → Colors l d → ℝ)
    (hM : ∀ n, RectangularForm (M n)) (hL : ∀ u v, 0 < L u v)
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) : RectangularForm L := by
  let P : A → PositiveMatrix (Colors k d) (Colors l d) :=
    fun n => ⟨M n, (hM n).positive⟩
  have hP : Tendsto P f (𝓝 (⟨L, hL⟩ : PositiveMatrix (Colors k d) (Colors l d))) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro u
    exact tendsto_pi_nhds.mpr (hlim u)
  exact (isClosed_rectangularForm i₀ j₀).mem_of_tendsto hP
    (Filter.Eventually.of_forall hM)

/-- Pull back both coordinates of an entrywise-positive matrix. -/
def pullbackPositive {I J U V : Type*} (r : U → I) (c : V → J)
    (M : PositiveMatrix I J) : PositiveMatrix U V :=
  ⟨fun u v => M.val (r u) (c v), fun u v => M.property (r u) (c v)⟩

lemma continuous_pullbackPositive {I J U V : Type*} (r : U → I) (c : V → J) :
    Continuous (pullbackPositive r c : PositiveMatrix I J → PositiveMatrix U V) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun u => continuous_pi fun v => continuous_entry (r u) (c v)

/-- Relative closedness is preserved by any fixed row and column orderings. -/
theorem isClosed_symmetricForm_reindex {I : Type*} {k d : ℕ}
    (i₀ : Fin k) (e : I ≃ Colors k d) :
    IsClosed {M : PositiveMatrix I I |
      SymmetricForm (fun u v => M.val (e.symm u) (e.symm v))} :=
  (isClosed_symmetricForm i₀).preimage (continuous_pullbackPositive e.symm e.symm)

theorem isClosed_rectangularForm_reindex {I J : Type*} {k l d : ℕ}
    (i₀ : Fin k) (j₀ : Fin l) (e : I ≃ Colors k d) (f : J ≃ Colors l d) :
    IsClosed {M : PositiveMatrix I J |
      RectangularForm (fun u v => M.val (e.symm u) (f.symm v))} :=
  (isClosed_rectangularForm i₀ j₀).preimage (continuous_pullbackPositive e.symm f.symm)

/-- Actual tensor membership allowing all dimension factorizations and color orderings. -/
def PermutedSymmetricForm {I : Type*} (M : I → I → ℝ) : Prop :=
  ∃ (k d : ℕ) (_i₀ : Fin k) (e : I ≃ Colors k d),
    SymmetricForm (fun u v => M (e.symm u) (e.symm v))

/-- A finite index type containing every possible positive symmetric tensor chart. -/
abbrev SymmetricCharts (I : Type*) [Fintype I] :=
  Σ k : Fin (Fintype.card I + 1), Σ d : Fin (Fintype.card I + 1),
    Fin k.val × (I ≃ Colors k.val d.val)

/-- Nonempty amplitude coordinates bound both dimensions by the color count. -/
lemma chart_dimension_bounds {I : Type*} [Fintype I] {k d : ℕ}
    (i₀ : Fin k) (e : I ≃ Colors k d) : k ≤ Fintype.card I ∧ d ≤ Fintype.card I := by
  classical
  have hcard : Fintype.card I = k * 2 ^ d := by
    simpa only [Colors, Cube, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool] using Fintype.card_congr e
  rw [hcard]
  constructor
  · exact Nat.le_mul_of_pos_right k (pow_pos (by decide) d)
  · exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
      (Nat.le_mul_of_pos_left (2 ^ d) (Fin.pos i₀))

theorem permutedSymmetricForm_iff_bounded {I : Type*} [Fintype I] (M : I → I → ℝ) :
    PermutedSymmetricForm M ↔ ∃ c : SymmetricCharts I,
      SymmetricForm (fun u v => M (c.2.2.2.symm u) (c.2.2.2.symm v)) := by
  constructor
  · rintro ⟨k, d, i₀, e, h⟩
    obtain ⟨hk, hd⟩ := chart_dimension_bounds i₀ e
    exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨d, Nat.lt_succ_of_le hd⟩, i₀, e⟩, h⟩
  · rintro ⟨⟨k, d, i₀, e⟩, h⟩
    exact ⟨k.val, d.val, i₀, e, h⟩

/-- The positive symmetric family is relatively closed even when dimensions
and color permutations are allowed to vary. The union is genuinely finite. -/
theorem isClosed_permutedSymmetricForm {I : Type*} [Fintype I] :
    IsClosed {M : PositiveMatrix I I | PermutedSymmetricForm M.val} := by
  classical
  simp only [permutedSymmetricForm_iff_bounded, Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  intro c
  exact isClosed_symmetricForm_reindex c.2.2.1 c.2.2.2

/-- Rectangular tensor membership with arbitrary dimension factorizations and
independent row and column orderings. -/
def PermutedRectangularForm {I J : Type*} (M : I → J → ℝ) : Prop :=
  ∃ (k l d : ℕ) (_i₀ : Fin k) (_j₀ : Fin l)
    (e : I ≃ Colors k d) (f : J ≃ Colors l d),
    RectangularForm (fun u v => M (e.symm u) (f.symm v))

/-- A finite index type containing every positive rectangular tensor chart. -/
abbrev RectangularCharts (I J : Type*) [Fintype I] [Fintype J] :=
  Σ k : Fin (Fintype.card I + 1), Σ l : Fin (Fintype.card J + 1),
    Σ d : Fin (Fintype.card I + 1),
      Fin k.val × Fin l.val × (I ≃ Colors k.val d.val) × (J ≃ Colors l.val d.val)

/-- Membership in the rectangular chart represented by one finite index. -/
def rectangularChartForm {I J : Type*} [Fintype I] [Fintype J]
    (c : RectangularCharts I J) (M : I → J → ℝ) : Prop :=
  RectangularForm (fun u v => M (c.2.2.2.2.2.1.symm u) (c.2.2.2.2.2.2.symm v))

theorem permutedRectangularForm_iff_bounded {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℝ) :
    PermutedRectangularForm M ↔ ∃ c : RectangularCharts I J, rectangularChartForm c M := by
  constructor
  · rintro ⟨k, l, d, i₀, j₀, e, f, h⟩
    obtain ⟨hk, hd⟩ := chart_dimension_bounds i₀ e
    obtain ⟨hl, _⟩ := chart_dimension_bounds j₀ f
    exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨l, Nat.lt_succ_of_le hl⟩,
      ⟨d, Nat.lt_succ_of_le hd⟩, i₀, j₀, e, f⟩, h⟩
  · rintro ⟨⟨k, l, d, i₀, j₀, e, f⟩, h⟩
    exact ⟨k.val, l.val, d.val, i₀, j₀, e, f, h⟩

/-- The positive rectangular family is relatively closed across all dimension
factorizations and all independent row and column permutations. -/
theorem isClosed_permutedRectangularForm {I J : Type*} [Fintype I] [Fintype J] :
    IsClosed {M : PositiveMatrix I J | PermutedRectangularForm M.val} := by
  classical
  simp only [permutedRectangularForm_iff_bounded, Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  rintro ⟨k, l, d, i₀, j₀, e, f⟩
  exact isClosed_rectangularForm_reindex i₀ j₀ e f

/-- The positive-chart predicate yields the paper's actual allowed block. -/
theorem PermutedSymmetricForm.allowedBlock {I : Type*} {M : I → I → ℝ}
    (h : PermutedSymmetricForm M) : Structures.AllowedBlock M := by
  obtain ⟨k, d, i₀, e, a, ρ, ha, hρ, hM⟩ := h
  refine Structures.AllowedBlock.positive k d (Fin.pos i₀) a ρ ha hρ e ?_
  intro u v
  simpa only [e.symm_apply_apply] using hM (e u) (e v)

/-- On an everywhere-positive matrix, the allowed-block definition is exactly
the positive tensor family. Its zero and bipartite alternatives are excluded
by their zero entries, rather than by an additional assumption. -/
theorem allowedBlock_iff_permutedSymmetricForm {I : Type*}
    (M : PositiveMatrix I I) :
    Structures.AllowedBlock M.val ↔ PermutedSymmetricForm M.val := by
  constructor
  · intro h
    cases h with
    | zero e hM =>
      have hpos := M.property (e.symm ()) (e.symm ())
      rw [hM] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
    | positive k d hk a ρ ha hρ e hM =>
      refine ⟨k, d, ⟨0, hk⟩, e, a, ρ, ha, hρ, ?_⟩
      intro u v
      simpa only [e.apply_symm_apply] using hM (e.symm u) (e.symm v)
    | bipartite k l d hk hl a b ρ ha hb hρ e hM =>
      let u := e.symm (Sum.inl (⟨0, hk⟩ : Fin k), (fun _ => false : Cube d))
      have hpos := M.property u u
      rw [hM] at hpos
      simp only [u, e.apply_symm_apply, Structures.bipartiteAmplitude, zero_mul] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
  · exact PermutedSymmetricForm.allowedBlock

/-- The complete positive-block case of Lemma A.5, for the original
`Structures.AllowedBlock` predicate and all possible tensor coordinates. -/
theorem isClosed_allowedBlock_positive {I : Type*} [Fintype I] :
    IsClosed {M : PositiveMatrix I I | Structures.AllowedBlock M.val} := by
  simpa only [allowedBlock_iff_permutedSymmetricForm] using
    (isClosed_permutedSymmetricForm (I := I))

/-- A relative closed-set statement on positive matrices implies preservation
under entrywise limits that remain positive. -/
theorem property_of_entrywise_tendsto {I J A : Type*}
    {f : Filter A} [f.NeBot] (P : (I → J → ℝ) → Prop)
    (hclosed : IsClosed {M : PositiveMatrix I J | P M.val})
    (M : A → I → J → ℝ) (L : I → J → ℝ)
    (hpos : ∀ n u v, 0 < M n u v) (hL : ∀ u v, 0 < L u v)
    (hM : ∀ n, P (M n))
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) : P L := by
  let Q : A → PositiveMatrix I J := fun n => ⟨M n, hpos n⟩
  have hQ : Tendsto Q f (𝓝 (⟨L, hL⟩ : PositiveMatrix I J)) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro u
    exact tendsto_pi_nhds.mpr (hlim u)
  exact hclosed.mem_of_tendsto hQ (Filter.Eventually.of_forall hM)

lemma PermutedSymmetricForm.positive {I : Type*} {M : I → I → ℝ}
    (h : PermutedSymmetricForm M) : ∀ u v, 0 < M u v := by
  obtain ⟨k, d, i₀, e, h⟩ := h
  intro u v
  simpa only [e.symm_apply_apply] using h.positive (e u) (e v)

lemma PermutedRectangularForm.positive {I J : Type*} {M : I → J → ℝ}
    (h : PermutedRectangularForm M) : ∀ u v, 0 < M u v := by
  obtain ⟨k, l, d, i₀, j₀, e, f, h⟩ := h
  intro u v
  simpa only [e.symm_apply_apply, f.symm_apply_apply] using h.positive (e u) (f v)

/-- Dimensions, amplitudes, tensor parameters, and color permutations may all
vary along the convergent family. Only the finite domain and positivity of
the limit are fixed. -/
theorem permutedSymmetricForm_of_tendsto {I A : Type*} [Fintype I]
    {f : Filter A} [f.NeBot] (M : A → I → I → ℝ) (L : I → I → ℝ)
    (hM : ∀ n, PermutedSymmetricForm (M n)) (hL : ∀ u v, 0 < L u v)
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) :
    PermutedSymmetricForm L :=
  property_of_entrywise_tendsto PermutedSymmetricForm isClosed_permutedSymmetricForm
    M L (fun n => (hM n).positive) hL hM hlim

/-- Rectangular tensor limits allow arbitrary dimensions and independent
row/column permutations at every index. -/
theorem permutedRectangularForm_of_tendsto {I J A : Type*} [Fintype I] [Fintype J]
    {f : Filter A} [f.NeBot] (M : A → I → J → ℝ) (L : I → J → ℝ)
    (hM : ∀ n, PermutedRectangularForm (M n)) (hL : ∀ u v, 0 < L u v)
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) :
    PermutedRectangularForm L :=
  property_of_entrywise_tendsto PermutedRectangularForm isClosed_permutedRectangularForm
    M L (fun n => (hM n).positive) hL hM hlim

/-- The complete positive-support case of Lemma A.5 as an entrywise limit
statement for the original allowed-block predicate. -/
theorem allowedBlock_of_tendsto_positive {I A : Type*} [Fintype I]
    {f : Filter A} [f.NeBot] (M : A → I → I → ℝ) (L : I → I → ℝ)
    (hpos : ∀ n u v, 0 < M n u v) (hL : ∀ u v, 0 < L u v)
    (hM : ∀ n, Structures.AllowedBlock (M n))
    (hlim : ∀ u v, Tendsto (fun n => M n u v) f (𝓝 (L u v))) :
    Structures.AllowedBlock L :=
  property_of_entrywise_tendsto Structures.AllowedBlock isClosed_allowedBlock_positive
    M L hpos hL hM hlim

/-- A matrix is strictly positive precisely on the specified support and is
zero everywhere else. No symmetry of the support is needed for this definition. -/
def HasSupport {I J : Type*} (P : I → J → Prop) (M : I → J → ℝ) : Prop :=
  (∀ i j, P i j → 0 < M i j) ∧ (∀ i j, ¬ P i j → M i j = 0)

/-- The relative space of matrices with a fixed positive support. -/
abbrev SupportMatrix {I J : Type*} (P : I → J → Prop) :=
  {M : I → J → ℝ // HasSupport P M}

lemma continuous_support_entry {I J : Type*} (P : I → J → Prop) (i : I) (j : J) :
    Continuous (fun M : SupportMatrix P => M.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- Positivity of one entry transfers between matrices on the same support. -/
lemma support_positive_transfer {I J : Type*} {P : I → J → Prop}
    (M N : SupportMatrix P) (i : I) (j : J) (h : 0 < M.val i j) : 0 < N.val i j := by
  apply N.property.1 i j
  by_contra hp
  rw [M.property.2 i j hp] at h
  exact (lt_irrefl 0) h

/-- A bipartite tensor chart in fixed coordinates, including both cross
orientations and the zero same-side entries. -/
def BipartiteForm {k l d : ℕ}
    (M : (Fin k ⊕ Fin l) × Cube d → (Fin k ⊕ Fin l) × Cube d → ℝ) : Prop :=
  ∃ (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ),
    (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ (∀ r, 0 < ρ r) ∧
    ∀ u v, M u v = Structures.bipartiteAmplitude a b u.1 v.1 * tensor ρ u.2 v.2

/-- Read the left-to-right rectangular cross block. -/
def crossBlock {k l d : ℕ}
    (M : (Fin k ⊕ Fin l) × Cube d → (Fin k ⊕ Fin l) × Cube d → ℝ) :
    Colors k d → Colors l d → ℝ :=
  fun u v => M (Sum.inl u.1, u.2) (Sum.inr v.1, v.2)

lemma BipartiteForm.cross_rectangular {k l d : ℕ}
    {M : (Fin k ⊕ Fin l) × Cube d → (Fin k ⊕ Fin l) × Cube d → ℝ}
    (h : BipartiteForm M) : RectangularForm (crossBlock M) := by
  obtain ⟨a, b, ρ, ha, hb, hρ, hM⟩ := h
  exact ⟨a, b, ρ, ha, hb, hρ, fun u v => hM (Sum.inl u.1, u.2) (Sum.inr v.1, v.2)⟩

/-- Positive cross entries suffice for canonical reconstruction of the whole
bipartite chart; the equations themselves impose both symmetry and same-side zeros. -/
theorem bipartiteForm_iff_reconstruction {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (M : (Fin k ⊕ Fin l) × Cube d → (Fin k ⊕ Fin l) × Cube d → ℝ)
    (hcross : ∀ u v, 0 < crossBlock M u v) :
    BipartiteForm M ↔ ∀ u v, M u v =
      Structures.bipartiteAmplitude (rowAmplitude i₀ j₀ (crossBlock M))
        (columnAmplitude i₀ (crossBlock M)) u.1 v.1 *
      tensor (rectangularParameter i₀ j₀ (crossBlock M)) u.2 v.2 := by
  constructor
  · rintro ⟨a, b, ρ, ha, hb, hρ, hM⟩
    have hx : crossBlock M = fun (u : Colors k d) (v : Colors l d) =>
        a u.1 * b v.1 * tensor ρ u.2 v.2 := by
      funext u v
      exact hM (Sum.inl u.1, u.2) (Sum.inr v.1, v.2)
    have hr : rectangularParameter i₀ j₀ (crossBlock M) = ρ := by
      rw [hx]
      exact funext (rectangularParameter_of_form i₀ j₀ a b ρ ha hb)
    have hp (i : Fin k) (j : Fin l) :
        rowAmplitude i₀ j₀ (crossBlock M) i * columnAmplitude i₀ (crossBlock M) j = a i * b j := by
      rw [hx]
      exact rectangularAmplitude_product_of_form i₀ j₀ a b ρ ha hb i j
    rintro ⟨u, x⟩ ⟨v, y⟩
    rw [hM, hr]
    cases u <;> cases v <;> simp only [Structures.bipartiteAmplitude, hp]
  · intro hM
    refine ⟨rowAmplitude i₀ j₀ (crossBlock M), columnAmplitude i₀ (crossBlock M),
      rectangularParameter i₀ j₀ (crossBlock M), ?_, ?_, ?_, hM⟩
    · intro i
      exact div_pos (hcross _ _) (hcross _ _)
    · intro j
      exact hcross _ _
    · intro r
      exact div_pos (hcross _ _) (hcross _ _)

lemma continuous_bipartiteAmplitude {X : Type*} [TopologicalSpace X] {k l : ℕ}
    (a : X → Fin k → ℝ) (b : X → Fin l → ℝ)
    (ha : ∀ i, Continuous (fun x => a x i)) (hb : ∀ j, Continuous (fun x => b x j))
    (u v : Fin k ⊕ Fin l) :
    Continuous (fun x => Structures.bipartiteAmplitude (a x) (b x) u v) := by
  cases u <;> cases v <;> simp only [Structures.bipartiteAmplitude]
  · exact continuous_const
  · exact (ha _).mul (hb _)
  · exact (ha _).mul (hb _)
  · exact continuous_const

/-- A fixed bipartite tensor chart is closed on any continuous matrix domain
where its cross-block entries stay positive. -/
theorem isClosed_bipartiteForm_of_cross_positive {X : Type*} [TopologicalSpace X]
    {k l d : ℕ} (i₀ : Fin k) (j₀ : Fin l)
    (M : X → (Fin k ⊕ Fin l) × Cube d → (Fin k ⊕ Fin l) × Cube d → ℝ)
    (hM : ∀ u v, Continuous (fun x => M x u v))
    (hcross : ∀ x u v, 0 < crossBlock (M x) u v) :
    IsClosed {x | BipartiteForm (M x)} := by
  let V : X → PositiveMatrix (Colors k d) (Colors l d) :=
    fun x => ⟨crossBlock (M x), hcross x⟩
  have hV : Continuous V := by
    apply Continuous.subtype_mk
    exact continuous_pi fun u => continuous_pi fun v =>
      hM (Sum.inl u.1, u.2) (Sum.inr v.1, v.2)
  have he : {x | BipartiteForm (M x)} = {x | ∀ u v, M x u v =
      Structures.bipartiteAmplitude (rowAmplitude i₀ j₀ (crossBlock (M x)))
        (columnAmplitude i₀ (crossBlock (M x))) u.1 v.1 *
      tensor (rectangularParameter i₀ j₀ (crossBlock (M x))) u.2 v.2} := by
    ext x
    exact bipartiteForm_iff_reconstruction i₀ j₀ (M x) (hcross x)
  rw [he]
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  exact isClosed_eq (hM u v)
    ((continuous_bipartiteAmplitude _ _
      (fun i => (continuous_rowAmplitude i₀ j₀ i).comp hV)
      (fun j => (continuous_columnAmplitude i₀ j).comp hV) u.1 v.1).mul
      (continuous_tensor _ (fun r => (continuous_rectangularParameter i₀ j₀ r).comp hV)
        u.2 v.2))

/-- The arbitrary-coordinate positive family is closed on every fixed support;
if it is nonempty, that support must be everywhere positive. -/
theorem isClosed_permutedSymmetricForm_support {I : Type*} [Fintype I]
    (P : I → I → Prop) :
    IsClosed {M : SupportMatrix P | PermutedSymmetricForm M.val} := by
  classical
  by_cases h : ∃ M : SupportMatrix P, PermutedSymmetricForm M.val
  · obtain ⟨M₀, h₀⟩ := h
    let f : SupportMatrix P → PositiveMatrix I I := fun M =>
      ⟨M.val, fun i j => support_positive_transfer M₀ M i j (h₀.positive i j)⟩
    have hf : Continuous f := Continuous.subtype_mk continuous_subtype_val _
    exact isClosed_permutedSymmetricForm.preimage hf
  · have he : {M : SupportMatrix P | PermutedSymmetricForm M.val} = ∅ := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hM => h ⟨M, hM⟩
    rw [he]
    exact isClosed_empty

/-- One bipartite ordering is relatively closed on every fixed support.
A witness, when one exists, forces the needed cross entries to be positive
throughout the relative domain. -/
theorem isClosed_bipartiteForm_support_reindex {I : Type*} {k l d : ℕ}
    (P : I → I → Prop) (i₀ : Fin k) (j₀ : Fin l)
    (e : I ≃ (Fin k ⊕ Fin l) × Cube d) :
    IsClosed {M : SupportMatrix P |
      BipartiteForm (fun u v => M.val (e.symm u) (e.symm v))} := by
  classical
  by_cases h : ∃ M : SupportMatrix P,
      BipartiteForm (fun u v => M.val (e.symm u) (e.symm v))
  · obtain ⟨M₀, h₀⟩ := h
    apply isClosed_bipartiteForm_of_cross_positive i₀ j₀
      (fun (M : SupportMatrix P) u v => M.val (e.symm u) (e.symm v))
    · intro u v
      exact continuous_support_entry P (e.symm u) (e.symm v)
    · intro M u v
      exact support_positive_transfer M₀ M _ _ (h₀.cross_rectangular.positive u v)
  · have he : {M : SupportMatrix P |
        BipartiteForm (fun u v => M.val (e.symm u) (e.symm v))} = ∅ := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hM => h ⟨M, hM⟩
    rw [he]
    exact isClosed_empty

/-- Bipartite tensor membership across every dimension and color ordering. -/
def PermutedBipartiteForm {I : Type*} (M : I → I → ℝ) : Prop :=
  ∃ (k l d : ℕ) (_i₀ : Fin k) (_j₀ : Fin l)
    (e : I ≃ (Fin k ⊕ Fin l) × Cube d),
    BipartiteForm (fun u v => M (e.symm u) (e.symm v))

/-- Finite indices for every possible bipartite chart on a fixed color set. -/
abbrev BipartiteCharts (I : Type*) [Fintype I] :=
  Σ k : Fin (Fintype.card I + 1), Σ l : Fin (Fintype.card I + 1),
    Σ d : Fin (Fintype.card I + 1),
      Fin k.val × Fin l.val × (I ≃ (Fin k.val ⊕ Fin l.val) × Cube d.val)

lemma bipartite_chart_dimension_bounds {I : Type*} [Fintype I] {k l d : ℕ}
    (i₀ : Fin k) (_j₀ : Fin l) (e : I ≃ (Fin k ⊕ Fin l) × Cube d) :
    k ≤ Fintype.card I ∧ l ≤ Fintype.card I ∧ d ≤ Fintype.card I := by
  classical
  have hcard : Fintype.card I = (k + l) * 2 ^ d := by
    simpa only [Cube, Fintype.card_prod, Fintype.card_sum, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool] using Fintype.card_congr e
  rw [hcard]
  have hkl : k + l ≤ (k + l) * 2 ^ d :=
    Nat.le_mul_of_pos_right (k + l) (pow_pos (by decide) d)
  refine ⟨(Nat.le_add_right k l).trans hkl, (Nat.le_add_left l k).trans hkl, ?_⟩
  exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.le_mul_of_pos_left (2 ^ d) ((Fin.pos i₀).trans_le (Nat.le_add_right k l)))

def bipartiteChartForm {I : Type*} [Fintype I]
    (c : BipartiteCharts I) (M : I → I → ℝ) : Prop :=
  BipartiteForm (fun u v => M (c.2.2.2.2.2.symm u) (c.2.2.2.2.2.symm v))

theorem permutedBipartiteForm_iff_bounded {I : Type*} [Fintype I] (M : I → I → ℝ) :
    PermutedBipartiteForm M ↔ ∃ c : BipartiteCharts I, bipartiteChartForm c M := by
  constructor
  · rintro ⟨k, l, d, i₀, j₀, e, h⟩
    obtain ⟨hk, hl, hd⟩ := bipartite_chart_dimension_bounds i₀ j₀ e
    exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨l, Nat.lt_succ_of_le hl⟩,
      ⟨d, Nat.lt_succ_of_le hd⟩, i₀, j₀, e⟩, h⟩
  · rintro ⟨⟨k, l, d, i₀, j₀, e⟩, h⟩
    exact ⟨k.val, l.val, d.val, i₀, j₀, e, h⟩

/-- The full bipartite family is relatively closed on every fixed support. -/
theorem isClosed_permutedBipartiteForm_support {I : Type*} [Fintype I]
    (P : I → I → Prop) :
    IsClosed {M : SupportMatrix P | PermutedBipartiteForm M.val} := by
  classical
  simp only [permutedBipartiteForm_iff_bounded, Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  rintro ⟨k, l, d, i₀, j₀, e⟩
  exact isClosed_bipartiteForm_support_reindex P i₀ j₀ e

/-- The three alternatives of the original allowed-block definition. -/
theorem allowedBlock_iff_three_forms {I : Type*} (M : I → I → ℝ) :
    Structures.AllowedBlock M ↔
      (∃ _e : I ≃ Unit, ∀ i j, M i j = 0) ∨
      PermutedSymmetricForm M ∨ PermutedBipartiteForm M := by
  constructor
  · intro h
    cases h with
    | zero e hM => exact Or.inl ⟨e, hM⟩
    | positive k d hk a ρ ha hρ e hM =>
      right
      left
      refine ⟨k, d, ⟨0, hk⟩, e, a, ρ, ha, hρ, ?_⟩
      intro u v
      simpa only [e.apply_symm_apply] using hM (e.symm u) (e.symm v)
    | bipartite k l d hk hl a b ρ ha hb hρ e hM =>
      right
      right
      refine ⟨k, l, d, ⟨0, hk⟩, ⟨0, hl⟩, e, a, b, ρ, ha, hb, hρ, ?_⟩
      intro u v
      simpa only [e.apply_symm_apply] using hM (e.symm u) (e.symm v)
  · rintro (⟨e, h⟩ | h | ⟨k, l, d, i₀, j₀, e, a, b, ρ, ha, hb, hρ, h⟩)
    · exact Structures.AllowedBlock.zero e h
    · exact h.allowedBlock
    · refine Structures.AllowedBlock.bipartite k l d (Fin.pos i₀) (Fin.pos j₀)
        a b ρ ha hb hρ e ?_
      intro u v
      simpa only [e.symm_apply_apply] using h (e u) (e v)

/-- Every allowed-block family is relatively closed on an arbitrary fixed
support. This includes all zero, positive, and bipartite alternatives and all
finite dimension factorizations and color orderings. -/
theorem isClosed_allowedBlock_support {I : Type*} [Fintype I] (P : I → I → Prop) :
    IsClosed {M : SupportMatrix P | Structures.AllowedBlock M.val} := by
  classical
  simp only [allowedBlock_iff_three_forms, Set.setOf_or]
  apply IsClosed.union
  · simp only [Set.setOf_exists, Set.setOf_forall]
    apply isClosed_iUnion_of_finite
    intro e
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (continuous_support_entry P i j) continuous_const
  · exact (isClosed_permutedSymmetricForm_support P).union
      (isClosed_permutedBipartiteForm_support P)


/-- Restriction to a specified part, retaining the fixed support. -/
def supportBlockRestriction {C : Type*} (P : C → C → Prop)
    {t : ℕ} (block : C → Fin t) (r : Fin t) (M : SupportMatrix P) :
    SupportMatrix (fun i j : {c // block c = r} => P i.val j.val) :=
  ⟨fun i j => M.val i.val j.val,
    ⟨fun i j h => M.property.1 i.val j.val h,
      fun i j h => M.property.2 i.val j.val h⟩⟩

lemma continuous_supportBlockRestriction {C : Type*} (P : C → C → Prop)
    {t : ℕ} (block : C → Fin t) (r : Fin t) :
    Continuous (supportBlockRestriction P block r) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j.val).comp ((continuous_apply i.val).comp continuous_subtype_val)

/-- Surjectivity bounds the number of direct-sum parts by the number of colors. -/
lemma partition_dimension_bound {C : Type*} [Fintype C] {t : ℕ}
    (block : C → Fin t) (hblock : Function.Surjective block) :
    t ≤ Fintype.card C := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective block hblock

/-- A finite type indexing every possible surjective partition of the colors. -/
abbrev SupportPartitions (C : Type*) [Fintype C] :=
  Σ t : Fin (Fintype.card C + 1), C → Fin t.val

theorem nonnegativeClass_iff_bounded_partitions {C : Type*} [Fintype C]
    (M : C → C → ℝ) :
    Structures.NonnegativeClass M ↔ ∃ c : SupportPartitions C,
      Function.Surjective c.2 ∧
      (∀ i j, c.2 i ≠ c.2 j → M i j = 0) ∧
      ∀ r, Structures.AllowedBlock (fun i j : {a // c.2 a = r} => M i.val j.val) := by
  constructor
  · rintro ⟨t, block, hsurj, hzero, hblocks⟩
    exact ⟨⟨⟨t, Nat.lt_succ_of_le (partition_dimension_bound block hsurj)⟩, block⟩,
      hsurj, hzero, hblocks⟩
  · rintro ⟨⟨t, block⟩, hsurj, hzero, hblocks⟩
    exact ⟨t.val, block, hsurj, hzero, hblocks⟩

/-- On a fixed support, closedness of each allowed block implies closedness of
its direct sums with a fixed partition. -/
theorem isClosed_fixedPartition_of_allowedBlock {C : Type*}
    (P : C → C → Prop) {t : ℕ} (block : C → Fin t)
    (hclosed : ∀ r : Fin t,
      IsClosed {M : SupportMatrix (fun i j : {c // block c = r} => P i.val j.val) |
        Structures.AllowedBlock M.val}) :
    IsClosed {M : SupportMatrix P |
      Function.Surjective block ∧
      (∀ i j, block i ≠ block j → M.val i j = 0) ∧
      ∀ r, Structures.AllowedBlock (fun i j : {c // block c = r} => M.val i.val j.val)} := by
  classical
  by_cases hsurj : Function.Surjective block
  · simp only [hsurj, true_and, Set.setOf_and]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro hij
      exact isClosed_eq
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
        continuous_const
    · simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro r
      exact (hclosed r).preimage (continuous_supportBlockRestriction P block r)
  · simp only [hsurj, false_and, Set.setOf_false]
    exact isClosed_empty

/-- Finite-partition assembly: the original nonnegative structural class is
relatively closed once the allowed-block theorem is available on each part. -/
theorem isClosed_nonnegativeClass_of_allowedBlock {C : Type*} [Fintype C]
    (P : C → C → Prop)
    (hclosed : ∀ (t : ℕ) (block : C → Fin t) (r : Fin t),
      IsClosed {M : SupportMatrix (fun i j : {c // block c = r} => P i.val j.val) |
        Structures.AllowedBlock M.val}) :
    IsClosed {M : SupportMatrix P | Structures.NonnegativeClass M.val} := by
  classical
  simp only [nonnegativeClass_iff_bounded_partitions, Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  intro c
  exact isClosed_fixedPartition_of_allowedBlock P c.2 (hclosed c.1.val c.2)

/-- A closed property on fixed-support matrices is preserved under entrywise
convergence to a matrix of the same support, for any nontrivial filter. -/
theorem support_property_of_entrywise_tendsto {I J A : Type*}
    {f : Filter A} [f.NeBot] (P : I → J → Prop) (Q : (I → J → ℝ) → Prop)
    (hclosed : IsClosed {M : SupportMatrix P | Q M.val})
    (M : A → I → J → ℝ) (L : I → J → ℝ)
    (hsupport : ∀ n, HasSupport P (M n)) (hL : HasSupport P L)
    (hM : ∀ n, Q (M n))
    (hlim : ∀ i j, Tendsto (fun n => M n i j) f (𝓝 (L i j))) : Q L := by
  let S : A → SupportMatrix P := fun n => ⟨M n, hsupport n⟩
  have hS : Tendsto S f (𝓝 (⟨L, hL⟩ : SupportMatrix P)) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hlim i)
  exact hclosed.mem_of_tendsto hS (Filter.Eventually.of_forall hM)

/-- The partition assembly as an entrywise-limit theorem for the original
structural predicate. The allowed-block closedness hypothesis is explicit. -/
theorem nonnegativeClass_of_tendsto_of_allowedBlock {C A : Type*} [Fintype C]
    {f : Filter A} [f.NeBot] (P : C → C → Prop)
    (hclosed : ∀ (t : ℕ) (block : C → Fin t) (r : Fin t),
      IsClosed {M : SupportMatrix (fun i j : {c // block c = r} => P i.val j.val) |
        Structures.AllowedBlock M.val})
    (M : A → C → C → ℝ) (L : C → C → ℝ)
    (hsupport : ∀ n, HasSupport P (M n)) (hL : HasSupport P L)
    (hM : ∀ n, Structures.NonnegativeClass (M n))
    (hlim : ∀ i j, Tendsto (fun n => M n i j) f (𝓝 (L i j))) :
    Structures.NonnegativeClass L :=
  support_property_of_entrywise_tendsto P Structures.NonnegativeClass
    (isClosed_nonnegativeClass_of_allowedBlock P hclosed) M L hsupport hL hM hlim

/-- **Lemma A.5 (limits with fixed support)**: for every fixed finite color set
and fixed support pattern, the exact structural class from Theorem 1.1 is
relatively closed in the space of matrices positive on that support.

The proof takes finite unions over actual tensor charts and over every bounded
surjective direct-sum partition. It therefore does not need a separate choice
or uniqueness theorem for connected support components. -/
theorem isClosed_nonnegativeClass_support {C : Type*} [Fintype C]
    (P : C → C → Prop) :
    IsClosed {M : SupportMatrix P | Structures.NonnegativeClass M.val} := by
  classical
  exact isClosed_nonnegativeClass_of_allowedBlock P
    (fun _ _ _ => isClosed_allowedBlock_support _)

/-- **Lemma A.5, entrywise-limit formulation.** Every matrix in the convergent
family belongs to the original `Structures.NonnegativeClass`, every matrix
has the fixed support, and the limit remains positive on that same support.
The conclusion is membership in that exact class, with dimensions, color
permutations, and direct-sum partitions allowed to vary along the family. -/
theorem nonnegativeClass_of_tendsto_fixedSupport {C A : Type*} [Fintype C]
    {f : Filter A} [f.NeBot] (P : C → C → Prop)
    (M : A → C → C → ℝ) (L : C → C → ℝ)
    (hsupport : ∀ n, HasSupport P (M n)) (hL : HasSupport P L)
    (hM : ∀ n, Structures.NonnegativeClass (M n))
    (hlim : ∀ i j, Tendsto (fun n => M n i j) f (𝓝 (L i j))) :
    Structures.NonnegativeClass L :=
  support_property_of_entrywise_tendsto P Structures.NonnegativeClass
    (isClosed_nonnegativeClass_support P) M L hsupport hL hM hlim

end PlanarHom.FixedChartClosedness
