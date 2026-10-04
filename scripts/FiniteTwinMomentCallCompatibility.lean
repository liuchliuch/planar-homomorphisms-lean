import PlanarHom.BipartiteFullTwinFinite
import PlanarHom.RectangularWeightedNormNormalization

/-! Check the observed moment API's argument order and expanded fiber-sum RHS
at the actual weighted normalization. This is a pure real-moment statement;
the absent field-source simulation and quotient_moment_real are not replaced. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FiniteTwinMomentCallCompatibility
open RectangularTwinQuotient RectangularWeightedNormNormalization BipartiteFullTwins
open RectangularSourceNormSimulation (block)
variable {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]

theorem weighted_moment_call
    (V : Matrix (Fin p) (Fin s) ℝ) (hV : ∀ i j, 0 < V i j)
    (μ : Fin p → ℝ) (ν : Fin s → ℝ)
    (hμ : ∀ i, 0 < μ i) (hν : ∀ j, 0 < ν j) (m : ℕ)
    (q : Quotient (Twins.rowSetoid (block (normalized V μ ν)))) :
    Twins.quotientWeight (block (normalized V μ ν))
      (fun i => Fin.addCases μ ν i *
        (Fin.addCases (rowNorm V ν) (columnNorm V μ) i) ^ (2 * m)) q =
      Sum.elim
        (fun r => ∑ x : {x // Quotient.mk (rowSetoid (normalized V μ ν)) x = r},
          μ x.val * (rowNorm V ν x.val) ^ (2 * m))
        (fun c => ∑ y : {y // Quotient.mk (columnSetoid (normalized V μ ν)) y = c},
          ν y.val * (columnNorm V μ y.val) ^ (2 * m))
        (finSideEquiv _ (normalized_pos _ hV _ _ hμ hν) q) := by
  exact quotientMoment_finSideEquiv _ (normalized_pos _ hV _ _ hμ hν)
    μ (rowNorm V ν) ν (columnNorm V μ) m q

end PlanarHom.FiniteTwinMomentCallCompatibility
