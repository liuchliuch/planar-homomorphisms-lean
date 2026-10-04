import PlanarHom.MaximumSupportRigidity
import PlanarHom.CubeDirections

/-!
# Opposite square weights from actual weighted shortest paths

The two length-two paths are constructed as genuine graph walks. Their proved
weight equality supplies the two scalar square identities, which force equal
opposite positive edge weights.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.MaximumLogarithmicSupport
open LogarithmicSupport ShortestPathWeights
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equal weights of actual shortest paths identify the two two-step products. -/
theorem two_step_products_eq_of_shortest_weights (L : Matrix V V ℝ) (G : SimpleGraph V)
    (i j u v : V) (hiu : G.Adj i u) (huj : G.Adj u j)
    (hiv : G.Adj i v) (hvj : G.Adj v j) (hd : G.dist i j = 2)
    (hweights : ∀ p q : ShortestPath G i j, walkWeight L p.val = walkWeight L q.val) :
    L i u * L u j = L i v * L v j := by
  let p : G.Walk i j := SimpleGraph.Walk.cons hiu (SimpleGraph.Walk.cons huj .nil)
  let q : G.Walk i j := SimpleGraph.Walk.cons hiv (SimpleGraph.Walk.cons hvj .nil)
  have hp : p.length = G.dist i j := by simp [p, hd]
  have hq : q.length = G.dist i j := by simp [q, hd]
  simpa [p, q, walkWeight] using hweights ⟨p, hp⟩ ⟨q, hq⟩

/-- Rational maximality supplies the exact two-step path-product equality. -/
theorem two_step_products_eq_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hmax : RationalSchurEdgeBound L hL) (i j u v : V)
    (hiu : (offDiagonalSupport L hL).Adj i u) (huj : (offDiagonalSupport L hL).Adj u j)
    (hiv : (offDiagonalSupport L hL).Adj i v) (hvj : (offDiagonalSupport L hL).Adj v j)
    (hd : (offDiagonalSupport L hL).dist i j = 2) :
    L i u * L u j = L i v * L v j :=
  two_step_products_eq_of_shortest_weights L _ i j u v hiu huj hiv hvj hd
    (shortest_paths_rigid_of_rational_maximality L hL hG hpositive hmax i j).2

/-- Both diagonals of a square give equal opposite edge weights, derived from
the numerical rational Schur edge-count bound. -/
theorem opposite_square_entries_eq_of_rational_maximality (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hmax : RationalSchurEdgeBound L hL) (v₁ v₂ v₃ v₄ : V)
    (h₁₂ : (offDiagonalSupport L hL).Adj v₁ v₂)
    (h₂₃ : (offDiagonalSupport L hL).Adj v₂ v₃)
    (h₃₄ : (offDiagonalSupport L hL).Adj v₃ v₄)
    (h₄₁ : (offDiagonalSupport L hL).Adj v₄ v₁)
    (hd₁₃ : (offDiagonalSupport L hL).dist v₁ v₃ = 2)
    (hd₂₄ : (offDiagonalSupport L hL).dist v₂ v₄ = 2) :
    L v₁ v₂ = L v₃ v₄ ∧ L v₂ v₃ = L v₄ v₁ := by
  have hsym (i j : V) : L i j = L j i := by simpa only [star_trivial] using hL.apply j i
  have h₁ := two_step_products_eq_of_rational_maximality L hL hG hpositive hmax
    v₁ v₃ v₂ v₄ h₁₂ h₂₃ h₄₁.symm h₃₄.symm hd₁₃
  have h₂ := two_step_products_eq_of_rational_maximality L hL hG hpositive hmax
    v₂ v₄ v₁ v₃ h₁₂.symm h₄₁.symm h₂₃ h₃₄ hd₂₄
  rw [hsym v₁ v₄, hsym v₄ v₃] at h₁
  rw [hsym v₂ v₁, hsym v₁ v₄] at h₂
  exact Boolean.opposite_weights_eq_of_square_products
    (hpositive v₁ v₂ h₁₂) (hpositive v₂ v₃ h₂₃)
    (hpositive v₃ v₄ h₃₄) (hpositive v₄ v₁ h₄₁) h₁ h₂

/-- A version directly usable when the actual logarithmic graph has been
identified with a fixed source graph. -/
theorem opposite_log_square_entries_eq (N : Matrix V V ℝ) (G : SimpleGraph V)
    (hEq : logSupport N = G) (hG : G.Connected)
    (hpositive : ∀ i j, G.Adj i j → 0 < EntropyCompletion.matrixLog N i j)
    (hmax : RationalSchurEdgeBound (EntropyCompletion.matrixLog N) IsSelfAdjoint.log)
    (v₁ v₂ v₃ v₄ : V) (h₁₂ : G.Adj v₁ v₂) (h₂₃ : G.Adj v₂ v₃)
    (h₃₄ : G.Adj v₃ v₄) (h₄₁ : G.Adj v₄ v₁)
    (hd₁₃ : G.dist v₁ v₃ = 2) (hd₂₄ : G.dist v₂ v₄ = 2) :
    EntropyCompletion.matrixLog N v₁ v₂ = EntropyCompletion.matrixLog N v₃ v₄ ∧
      EntropyCompletion.matrixLog N v₂ v₃ = EntropyCompletion.matrixLog N v₄ v₁ := by
  have hgraph : offDiagonalSupport (EntropyCompletion.matrixLog N) IsSelfAdjoint.log = G := hEq
  apply opposite_square_entries_eq_of_rational_maximality (EntropyCompletion.matrixLog N)
    IsSelfAdjoint.log (by simpa only [hgraph] using hG)
    (fun i j h => hpositive i j (hgraph ▸ h)) hmax v₁ v₂ v₃ v₄
  · simpa only [hgraph] using h₁₂
  · simpa only [hgraph] using h₂₃
  · simpa only [hgraph] using h₃₄
  · simpa only [hgraph] using h₄₁
  · simpa only [hgraph] using hd₁₃
  · simpa only [hgraph] using hd₂₄

end PlanarHom.MaximumLogarithmicSupport
