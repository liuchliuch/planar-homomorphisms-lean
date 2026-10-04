import PlanarHom.MaximumSupportRigidity
import PlanarHom.ShortestPathCommonNeighbors
import PlanarHom.CartesianGeometry

/-!
# Local clique geometry from explicit rational maximality bounds

The two-neighbor count is derived from the actual shortest-path theorem; its
nonadjacency is derived from the actual Wheatstone logarithm. No local graph
condition is assumed. The remaining rational candidate-count bounds are named
explicitly and are not claimed to have been proved for the paper's available
matrix family until its computational reduction closure is constructed.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.MaximumLogarithmicSupport
open LogarithmicSupport MatrixLogCoefficients WheatstoneCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The eventual edge-count bound for the actual rational Wheatstone candidates. -/
def RationalWheatstoneEdgeBound (G : SimpleGraph V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
    (wheatstoneMatrix G q).PosDef → (∀ a b, 0 < wheatstoneMatrix G q a b) →
    (logSupport (wheatstoneMatrix G q)).edgeFinset.card ≤ G.edgeFinset.card

/-- Rational maximality for Schur and Wheatstone candidates forces exactly two
nonadjacent common neighbors at every distance-two pair. -/
theorem twoCommonNeighbors_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hschur : RationalSchurEdgeBound L hL)
    (hwheat : RationalWheatstoneEdgeBound (offDiagonalSupport L hL)) :
    CartesianGeometry.TwoCommonNeighbors (offDiagonalSupport L hL) := by
  intro i j hd
  have hcard := (shortest_paths_rigid_of_rational_maximality L hL hG hpositive hschur i j).1
  obtain ⟨u, v, huv, hcommon⟩ :=
    ShortestPathWeights.exists_two_commonNeighbors_of_shortestPath_card_factorial
      (offDiagonalSupport L hL) hd hcard
  refine ⟨u, v, huv, ?_, hcommon⟩
  exact nonadjacent_commonNeighbors_of_rational_log_edge_bound
    (offDiagonalSupport L hL) hG hd huv hcommon hwheat

/-- The neighborhood-clique condition is derived as well, not assumed. -/
theorem neighborhoodCliques_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hschur : RationalSchurEdgeBound L hL)
    (hwheat : RationalWheatstoneEdgeBound (offDiagonalSupport L hL)) :
    CartesianGeometry.NeighborhoodCliques (offDiagonalSupport L hL) :=
  (twoCommonNeighbors_of_rational_maximality L hL hG hpositive hschur hwheat).neighborhoodCliques

/-- The chapter-four geometry assembled from the explicit candidate bounds and
initial distance-kernel sparsity. Availability/maximality still has to supply
these concrete premises for the paper's fixed source family. -/
theorem cartesian_product_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hschur : RationalSchurEdgeBound L hL)
    (hwheat : RationalWheatstoneEdgeBound (offDiagonalSupport L hL))
    (hsparse : EntropyCompletion.initiallyLogSparse (offDiagonalSupport L hL)) :
    ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
      Nonempty ((offDiagonalSupport L hL) ≃g CartesianGeometry.hammingGraph (fun i => Fin (s i))) := by
  have htwo := twoCommonNeighbors_of_rational_maximality L hL hG hpositive hschur hwheat
  exact CartesianGeometry.cartesian_product_characterization (offDiagonalSupport L hL) hG
    (fun x hx hx1 => (KernelContinuation.posDef_distanceKernel _ hG hsparse hx hx1).posSemidef)
    htwo.neighborhoodCliques htwo

end PlanarHom.MaximumLogarithmicSupport
