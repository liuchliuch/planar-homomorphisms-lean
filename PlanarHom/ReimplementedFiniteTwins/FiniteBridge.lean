import PlanarHom.BipartiteFullTwinSideEquiv
import PlanarHom.ReimplementedFiniteTwins.QuotientReindex
import Mathlib.Logic.Equiv.Fin.Basic

/-!
New finite-index bridge reconstruction, not recovered historical source.

The matrix here is explicitly the pullback of the existing real bipartite
double along `finSumFinEquiv.symm`. The real numerical-row quotient and the
original rectangular side quotients are retained literally.

This internal namespace retains the independently proved construction.
The adapter proves literal equality to a newly defined finite bipartite block.
No unavailable source-simulation algorithm is replaced or asserted.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.BipartiteFullTwins.ReconstructedFinite

open RectangularTwinQuotient
open Twins.ReconstructedReindex

variable {p s : ℕ}

/-- The sum-indexed real double in its standard finite index chart. -/
def finiteDouble (C : Matrix (Fin p) (Fin s) ℝ) :
    Matrix (Fin (p + s)) (Fin (p + s)) ℝ :=
  matrix (double C) finSumFinEquiv.symm

theorem finiteDouble_symmetric (C : Matrix (Fin p) (Fin s) ℝ) :
    ∀ i j, finiteDouble C i j = finiteDouble C j i :=
  symmetric (double C) finSumFinEquiv.symm (double_symmetric C)

/-- The same actual row class is transported to its actual rectangular side. -/
def finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ) (hC : ∀ i j, 0 < C i j) :
    Quotient (Twins.rowSetoid (finiteDouble C)) ≃ Rows C ⊕ Columns C :=
  (quotientEquiv (double C) finSumFinEquiv.symm).trans (sideEquiv C hC)

@[simp] theorem finSideEquiv_mk (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j) (i : Fin (p + s)) :
    finSideEquiv C hC (Quotient.mk _ i) = sideClass C (finSumFinEquiv.symm i) := rfl

theorem quotientMatrix_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j)
    (a b : Quotient (Twins.rowSetoid (finiteDouble C))) :
    Twins.quotientMatrix (finiteDouble C) (finiteDouble_symmetric C) a b =
      double (core C) (finSideEquiv C hC a) (finSideEquiv C hC b) := by
  exact (quotientMatrix_transport (double C) finSumFinEquiv.symm
    (double_symmetric C) a b).trans (quotientMatrix_sideEquiv C hC _ _)

theorem addCases_eq_sumElim (μ : Fin p → ℝ) (ν : Fin s → ℝ) (i : Fin (p + s)) :
    Fin.addCases μ ν i = Sum.elim μ ν (finSumFinEquiv.symm i) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

/-- Each side retains its own literal fiber sum, with no relation imposed on
the two masses or the two side cardinalities. -/
theorem quotientWeight_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j) (μ : Fin p → ℝ) (ν : Fin s → ℝ)
    (a : Quotient (Twins.rowSetoid (finiteDouble C))) :
    Twins.quotientWeight (finiteDouble C) (Fin.addCases μ ν) a =
      sideWeight C μ ν (finSideEquiv C hC a) := by
  have hw : Fin.addCases μ ν = fun i => Sum.elim μ ν (finSumFinEquiv.symm i) :=
    funext (addCases_eq_sumElim μ ν)
  rw [hw]
  exact (quotientWeight_transport (double C) finSumFinEquiv.symm
    (Sum.elim μ ν) a).trans (quotientWeight_sideEquiv C hC μ ν _)

/-- Every moment uses precisely the same quotient equivalence as the matrix.
No positivity or equality hypothesis is added for the original weights or
the scales. In particular, the zeroth moment is the weighted class mass. -/
theorem quotientMoment_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j)
    (μ α : Fin p → ℝ) (ν β : Fin s → ℝ) (m : ℕ)
    (a : Quotient (Twins.rowSetoid (finiteDouble C))) :
    Twins.quotientWeight (finiteDouble C)
      (fun i => Fin.addCases μ ν i * (Fin.addCases α β i) ^ (2 * m)) a =
      Sum.elim
        (fun r => ∑ x : {x // Quotient.mk (rowSetoid C) x = r},
          μ x.val * (α x.val) ^ (2 * m))
        (fun c => ∑ y : {y // Quotient.mk (columnSetoid C) y = c},
          ν y.val * (β y.val) ^ (2 * m))
        (finSideEquiv C hC a) := by
  have hw : (fun i => Fin.addCases μ ν i * (Fin.addCases α β i) ^ (2 * m)) =
      Fin.addCases (fun x => μ x * (α x) ^ (2 * m))
        (fun y => ν y * (β y) ^ (2 * m)) := by
    funext i
    refine Fin.addCases (fun x => ?_) (fun y => ?_) i <;> simp
  rw [hw]
  exact quotientWeight_finSideEquiv C hC _ _ a

end PlanarHom.BipartiteFullTwins.ReconstructedFinite
