import PlanarHom.RectangularBipartiteBlock
import PlanarHom.ReimplementedFiniteTwins.FiniteBridge

/-!
# Finite bipartite numerical-twin transport — NEW reconstruction

This implements the finite quotient interface required by surviving consumers,
using the complete historical rectangular quotient and side-equivalence modules.
The literal finite block is explicitly defined and proved equal to the finite
pullback double. No equality of sides or background masses is imposed.

This is not recovered historical source, nor a source-simulation algorithm.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.BipartiteFullTwins

open RectangularTwinQuotient
open RectangularSourceNormSimulation (block block_symm)
variable {p s : ℕ}

theorem fin_block_entry (C : Matrix (Fin p) (Fin s) ℝ) (i j : Fin (p + s)) :
    block C i j = double C (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := rfl

theorem block_eq_finiteDouble (C : Matrix (Fin p) (Fin s) ℝ) :
    block C = ReconstructedFinite.finiteDouble C := rfl

def finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ) (hC : ∀ i j, 0 < C i j) :
    Quotient (Twins.rowSetoid (block C)) ≃ Rows C ⊕ Columns C :=
  ReconstructedFinite.finSideEquiv C hC

@[simp] theorem finSideEquiv_mk (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j) (i : Fin (p + s)) :
    finSideEquiv C hC (Quotient.mk _ i) = sideClass C (finSumFinEquiv.symm i) := rfl

theorem quotientMatrix_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j) (a b : Quotient (Twins.rowSetoid (block C))) :
    Twins.quotientMatrix (block C) (block_symm C) a b =
      double (core C) (finSideEquiv C hC a) (finSideEquiv C hC b) :=
  ReconstructedFinite.quotientMatrix_finSideEquiv C hC a b

theorem quotientWeight_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j) (μ : Fin p → ℝ) (ν : Fin s → ℝ)
    (a : Quotient (Twins.rowSetoid (block C))) :
    Twins.quotientWeight (block C) (Fin.addCases μ ν) a =
      sideWeight C μ ν (finSideEquiv C hC a) :=
  ReconstructedFinite.quotientWeight_finSideEquiv C hC μ ν a

theorem quotientMoment_finSideEquiv (C : Matrix (Fin p) (Fin s) ℝ)
    (hC : ∀ i j, 0 < C i j)
    (μ α : Fin p → ℝ) (ν β : Fin s → ℝ) (m : ℕ)
    (a : Quotient (Twins.rowSetoid (block C))) :
    Twins.quotientWeight (block C)
      (fun i => Fin.addCases μ ν i * (Fin.addCases α β i) ^ (2 * m)) a =
      Sum.elim
        (fun r => ∑ x : {x // Quotient.mk (rowSetoid C) x = r},
          μ x.val * (α x.val) ^ (2 * m))
        (fun c => ∑ y : {y // Quotient.mk (columnSetoid C) y = c},
          ν y.val * (β y.val) ^ (2 * m))
        (finSideEquiv C hC a) :=
  ReconstructedFinite.quotientMoment_finSideEquiv C hC μ α ν β m a

end PlanarHom.BipartiteFullTwins
