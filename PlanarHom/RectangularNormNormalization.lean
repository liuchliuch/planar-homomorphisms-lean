import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rectangular Euclidean-norm normalization — NEW implementation

This is new proof code, not recovered historical source. The definitions are
specified in the proof of Theorem 9.1 of the cited paper (printed page 65),
whose SHA256 is 366b92c0dfafc076a43751b04cae1296562d3b87ec97a9b27d8a25085dc407f5.
They also match the surviving weighted implementation at unit backgrounds.

The historical namespace is deliberately implemented here to test its actual
unchanged consumers in an isolated overlay. No source in the evidence tree or
baseline is edited. These results concern real matrices only: no algorithm,
gadget-availability, hardness, or bit-complexity claim is made.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.RectangularNormNormalization

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Euclidean norm of one original row. -/
def rowNorm (V : Matrix X Y ℝ) (x : X) : ℝ := Real.sqrt (∑ y, (V x y)^2)

/-- Euclidean norm of one original column. -/
def columnNorm (V : Matrix X Y ℝ) (y : Y) : ℝ := Real.sqrt (∑ x, (V x y)^2)

/-- Divide by the product of the two original norms, not successive normalizations. -/
def normalized (V : Matrix X Y ℝ) : Matrix X Y ℝ :=
  fun x y => V x y / (rowNorm V x * columnNorm V y)

omit [Fintype X] in
theorem rowNorm_nonneg (V : Matrix X Y ℝ) (x : X) : 0 ≤ rowNorm V x :=
  Real.sqrt_nonneg _

omit [Fintype Y] in
theorem columnNorm_nonneg (V : Matrix X Y ℝ) (y : Y) : 0 ≤ columnNorm V y :=
  Real.sqrt_nonneg _

omit [Fintype X] in
theorem rowNorm_sq (V : Matrix X Y ℝ) (x : X) :
    (rowNorm V x)^2 = ∑ y, (V x y)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [Fintype Y] in
theorem columnNorm_sq (V : Matrix X Y ℝ) (y : Y) :
    (columnNorm V y)^2 = ∑ x, (V x y)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

variable [Nonempty X] [Nonempty Y]

omit [Fintype X] [Nonempty X] in
theorem rowNorm_pos (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (x : X) :
    0 < rowNorm V x :=
  Real.sqrt_pos.mpr
    (Finset.sum_pos (fun y _ => sq_pos_of_pos (hV x y)) Finset.univ_nonempty)

omit [Fintype Y] [Nonempty Y] in
theorem columnNorm_pos (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (y : Y) :
    0 < columnNorm V y :=
  Real.sqrt_pos.mpr
    (Finset.sum_pos (fun x _ => sq_pos_of_pos (hV x y)) Finset.univ_nonempty)

theorem normalized_pos (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) :
    ∀ x y, 0 < normalized V x y := fun x y =>
  div_pos (hV x y) (mul_pos (rowNorm_pos V hV x) (columnNorm_pos V hV y))

/-- Undoing the column scale leaves a unit Euclidean row. -/
theorem row_unit (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (x : X) :
    (∑ y, (normalized V x y * columnNorm V y)^2) = 1 := by
  have h (y : Y) : normalized V x y * columnNorm V y = V x y / rowNorm V x := by
    unfold normalized
    field_simp [ne_of_gt (columnNorm_pos V hV y), ne_of_gt (rowNorm_pos V hV x)]
  simp_rw [h, div_pow]
  rw [← Finset.sum_div, ← rowNorm_sq V x]
  exact div_self (pow_ne_zero _ (ne_of_gt (rowNorm_pos V hV x)))

/-- Undoing the row scale leaves a unit Euclidean column. -/
theorem column_unit (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (y : Y) :
    (∑ x, (normalized V x y * rowNorm V x)^2) = 1 := by
  have h (x : X) : normalized V x y * rowNorm V x = V x y / columnNorm V y := by
    unfold normalized
    field_simp [ne_of_gt (columnNorm_pos V hV y), ne_of_gt (rowNorm_pos V hV x)]
  simp_rw [h, div_pow]
  rw [← Finset.sum_div, ← columnNorm_sq V y]
  exact div_self (pow_ne_zero _ (ne_of_gt (columnNorm_pos V hV y)))

omit [Fintype X] [Nonempty X] in
/-- A common scaling of coordinates preserves the scalar test for proportional rows. -/
theorem proportional_unit_rows (C : Matrix X Y ℝ) (hC : ∀ x y, 0 < C x y)
    (scale : Y → ℝ) (hunit : ∀ x, ∑ y, (C x y * scale y)^2 = 1)
    (x x' : X) (t : ℝ) (h : ∀ y, C x y = t * C x' y) :
    t = 1 ∧ C x = C x' := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have ht : 0 < t := by
    have := h y
    have := hC x y
    have := hC x' y
    nlinarith
  have he : 1 = t^2 := by
    calc
      1 = ∑ y, (C x y * scale y)^2 := (hunit x).symm
      _ = t^2 * (∑ y, (C x' y * scale y)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [h y]
        ring
      _ = t^2 := by rw [hunit, mul_one]
  have ht1 : t = 1 := by nlinarith
  exact ⟨ht1, funext (fun y => by simpa only [ht1, one_mul] using h y)⟩

theorem reconstruct (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (x : X) (y : Y) :
    V x y = rowNorm V x * columnNorm V y * normalized V x y := by
  unfold normalized
  field_simp [ne_of_gt (columnNorm_pos V hV y), ne_of_gt (rowNorm_pos V hV x)]

theorem normalized_proportional_rows (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (x x' : X) (t : ℝ) (h : ∀ y, normalized V x y = t * normalized V x' y) :
    t = 1 ∧ normalized V x = normalized V x' :=
  proportional_unit_rows _ (normalized_pos V hV) (columnNorm V)
    (row_unit V hV) x x' t h

theorem normalized_proportional_columns (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (y y' : Y) (t : ℝ) (h : ∀ x, normalized V x y = t * normalized V x y') :
    t = 1 ∧ (normalized V).transpose y = (normalized V).transpose y' :=
  proportional_unit_rows (normalized V).transpose
    (fun y x => normalized_pos V hV x y) (rowNorm V) (column_unit V hV) y y' t h

/-- Original proportional rows become equal after normalization, as in Theorem 9.1. -/
theorem normalized_rows_eq_of_proportional (V : Matrix X Y ℝ)
    (hV : ∀ x y, 0 < V x y) (x x' : X) (t : ℝ)
    (h : ∀ y, V x y = t * V x' y) : normalized V x = normalized V x' := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have ht : 0 < t := by
    have := h y
    have := hV x y
    have := hV x' y
    nlinarith
  have hs : (rowNorm V x)^2 = t^2 * (rowNorm V x')^2 := by
    rw [rowNorm_sq, rowNorm_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [h j]
    ring
  have hn : rowNorm V x = t * rowNorm V x' := by
    have := rowNorm_pos V hV x
    have := rowNorm_pos V hV x'
    have := mul_pos ht (rowNorm_pos V hV x')
    nlinarith [sq_nonneg (rowNorm V x - t * rowNorm V x')]
  funext j
  unfold normalized
  rw [h j, hn]
  field_simp [ne_of_gt ht, ne_of_gt (rowNorm_pos V hV x'),
    ne_of_gt (columnNorm_pos V hV j)]

/-- Original proportional columns likewise become equal. -/
theorem normalized_columns_eq_of_proportional (V : Matrix X Y ℝ)
    (hV : ∀ x y, 0 < V x y) (y y' : Y) (t : ℝ)
    (h : ∀ x, V x y = t * V x y') :
    (normalized V).transpose y = (normalized V).transpose y' := by
  have he := normalized_rows_eq_of_proportional V.transpose
    (fun j i => hV i j) y y' t h
  funext i
  simpa only [normalized, rowNorm, columnNorm, Matrix.transpose_apply, mul_comm] using congrFun he i

end PlanarHom.RectangularNormNormalization
