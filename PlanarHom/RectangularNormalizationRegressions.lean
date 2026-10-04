import PlanarHom.RectangularTwinQuotient
import PlanarHom.RectangularWeightedNormNormalization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! NEW regression tests. The two imported historical consumers are byte-identical copies. -/
noncomputable section
open Classical
open scoped BigOperators
namespace RectangularNormalizationRegressions
open PlanarHom.RectangularNormNormalization
open PlanarHom.RectangularTwinQuotient

/-- A one-by-one matrix is divided by both original norms. -/
theorem singleton_two : normalized (fun _ _ : Fin 1 => (2 : ℝ)) 0 0 = 1 / 2 := by
  norm_num [normalized, rowNorm, columnNorm]

/-- Unequal side cardinalities affect their own original norms independently. -/
theorem rectangular_two_by_three :
    rowNorm (fun (_ : Fin 2) (_ : Fin 3) => (1 : ℝ)) 0 = Real.sqrt 3 ∧
    columnNorm (fun (_ : Fin 2) (_ : Fin 3) => (1 : ℝ)) 0 = Real.sqrt 2 := by
  norm_num [rowNorm, columnNorm]

/-- Definition-level zero-dimensional boundary: no positivity conclusion is assumed. -/
theorem empty_rows (V : Matrix (Fin 0) (Fin 3) ℝ) (j : Fin 3) : columnNorm V j = 0 := by
  simp [columnNorm]

theorem empty_columns (V : Matrix (Fin 2) (Fin 0) ℝ) (i : Fin 2) : rowNorm V i = 0 := by
  simp [rowNorm]

/-- Positivity is not needed to define the totalized normalization at a zero matrix. -/
theorem zero_matrix : normalized (fun (_ : Fin 2) (_ : Fin 3) => (0 : ℝ)) = 0 := by
  ext i j
  simp [normalized, rowNorm, columnNorm]

/-- Literal surviving unit-background correspondence, including possible empty sides. -/
theorem weighted_unit_eq {X Y : Type} [Fintype X] [Fintype Y] (V : Matrix X Y ℝ) :
    PlanarHom.RectangularWeightedNormNormalization.normalized V (fun _ => 1) (fun _ => 1) =
      normalized V := by
  ext x y
  simp [PlanarHom.RectangularWeightedNormNormalization.normalized,
    PlanarHom.RectangularWeightedNormNormalization.rowNorm,
    PlanarHom.RectangularWeightedNormNormalization.columnNorm, normalized, rowNorm, columnNorm]

variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Every real scalar is covered, so zero/negative proportionalities are ruled out. -/
theorem arbitrary_scalar (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (x x' : X) (t : ℝ) (h : ∀ y, normalized V x y = t * normalized V x' y) : t = 1 :=
  (normalized_proportional_rows V hV x x' t h).1

/-- The original quotient consumer recovers entries through its actual core. -/
theorem quotient_reconstruct (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y) (x : X) (y : Y) :
    V x y = rowNorm V x * columnNorm V y *
      core (normalized V) (Quotient.mk (rowSetoid (normalized V)) x)
        (Quotient.mk (columnSetoid (normalized V)) y) :=
  original_entry_from_core V hV x y

/-- The original quotient consumer excludes distinct proportional row classes. -/
theorem quotient_row_rigidity (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (r r' : Rows (normalized V)) (t : ℝ)
    (h : ∀ s, core (normalized V) r s = t * core (normalized V) r' s) : t = 1 ∧ r = r' :=
  normalized_core_no_proportional_rows V hV r r' t h

theorem quotient_column_rigidity (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (s s' : Columns (normalized V)) (t : ℝ)
    (h : ∀ r, core (normalized V) r s = t * core (normalized V) r s') : t = 1 ∧ s = s' :=
  normalized_core_no_proportional_columns V hV s s' t h

/-- At order zero the class mass retains multiplicity, not merely one representative. -/
theorem row_zero_moment (V : Matrix X Y ℝ) (r : Rows (normalized V)) :
    rowClassMass V 0 r = Fintype.card {x // Quotient.mk (rowSetoid (normalized V)) x = r} :=
  rowClassMass_zero V r

theorem column_zero_moment (V : Matrix X Y ℝ) (s : Columns (normalized V)) :
    columnClassMass V 0 s = Fintype.card {y // Quotient.mk (columnSetoid (normalized V)) y = s} :=
  columnClassMass_zero V s

/-- Distinct proportional original rows are permitted, and merge after normalization. -/
theorem proportional_original_rows (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (x x' : X) (t : ℝ) (h : ∀ y, V x y = t * V x' y) :
    Quotient.mk (rowSetoid (normalized V)) x = Quotient.mk (rowSetoid (normalized V)) x' :=
  Quotient.sound (normalized_rows_eq_of_proportional V hV x x' t h)

theorem proportional_original_columns (V : Matrix X Y ℝ) (hV : ∀ x y, 0 < V x y)
    (y y' : Y) (t : ℝ) (h : ∀ x, V x y = t * V x y') :
    Quotient.mk (columnSetoid (normalized V)) y = Quotient.mk (columnSetoid (normalized V)) y' :=
  Quotient.sound (normalized_columns_eq_of_proportional V hV y y' t h)

end RectangularNormalizationRegressions
