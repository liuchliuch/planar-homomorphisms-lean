import PlanarHom.MaximumLogarithmicSupport
import PlanarHom.RationalWeightedPaths

/-!
# Weighted shortest paths from an explicit rational maximum-edge bound

All analytic coefficients, path products and rational-sampling steps are proved.
The remaining premise is the numerical maximality bound for admissible rational
Schur candidates; establishing it for the paper's jointly available family still
requires the spectral/gadget reduction construction.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology BigOperators Matrix.Norms.Operator
namespace PlanarHom.MaximumLogarithmicSupport
open LogarithmicSupport MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact rational candidate edge-count bound, rather than an assumed
shortest-path identity or support-preservation conclusion. -/
def RationalSchurEdgeBound (L : Matrix V V ℝ) (hL : L.IsHermitian) : Prop :=
  ∀ s : ℕ, 0 < s → Even s → ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℚ, 0 < q → (q : ℝ) < ε → (schurExp L s q).PosDef →
      (offDiagonalSupport (schurExp L s q) (schurExp_isHermitian L hL s q)).Connected →
      (∀ i j, 0 ≤ schurExp L s q i j) →
      (logSupport (schurExp L s q)).edgeFinset.card ≤ (offDiagonalSupport L hL).edgeFinset.card

/-- The complete weighted-shortest-path conclusion follows from the explicit
rational maximality bound, with no real-parameter or desired-coefficient premise. -/
theorem shortest_paths_rigid_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hmax : RationalSchurEdgeBound L hL) (i j : V) :
    Fintype.card (ShortestPathWeights.ShortestPath (offDiagonalSupport L hL) i j) =
        ((offDiagonalSupport L hL).dist i j).factorial ∧
      ∀ p q : ShortestPathWeights.ShortestPath (offDiagonalSupport L hL) i j,
        ShortestPathWeights.walkWeight L p.val = ShortestPathWeights.walkWeight L q.val := by
  letI : Nonempty V := hG.nonempty
  apply shortest_paths_rigid_of_rational_schur_log_support L hL hG hpositive _ i j
  intro s hs heven
  obtain ⟨δ, hδ, hsupport⟩ := rational_schur_logSupport_eq_of_maximal L hL hG s hs heven
    (hmax s hs heven)
  refine ⟨δ, hδ, ?_⟩
  intro q hq hqδ a b hab hn
  obtain ⟨_, heq, _⟩ := hsupport q (by exact_mod_cast hq) hqδ
  by_contra hne
  have hedge : (logSupport (schurExp L s q)).Adj a b := ⟨hab, hne⟩
  exact hn (heq ▸ hedge)

/-- Squaring the entries of a rational spectral exponential produces a PD
replacement with exactly the same logarithmic graph and positive logarithmic
entries on every edge, under the explicit candidate maximum bound. -/
theorem exists_positive_log_replacement (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (offDiagonalSupport L hL).Connected) (hmax : RationalSchurEdgeBound L hL) :
    ∃ q : ℚ, 0 < q ∧ (schurExp L 2 q).PosDef ∧
      (∀ i j, 0 ≤ schurExp L 2 q i j) ∧
      logSupport (schurExp L 2 q) = offDiagonalSupport L hL ∧
      ∀ i j, (logSupport (schurExp L 2 q)).Adj i j →
        0 < EntropyCompletion.matrixLog (schurExp L 2 q) i j := by
  obtain ⟨δ, hδ, hsupport⟩ := rational_schur_logSupport_eq_of_maximal L hL hG 2 (by decide)
    (by decide) (hmax 2 (by decide) (by decide))
  obtain ⟨q, hq, hqδ⟩ := exists_rat_btwn hδ
  have hq' : 0 < q := by exact_mod_cast hq
  obtain ⟨hpd, heq, hpos⟩ := hsupport q hq' hqδ
  exact ⟨q, hq', hpd, fun i j => sq_nonneg _, heq, hpos⟩

end PlanarHom.MaximumLogarithmicSupport
