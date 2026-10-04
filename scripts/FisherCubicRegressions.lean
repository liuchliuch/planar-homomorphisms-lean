import PlanarHom.FisherCubicWeighted

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.FisherCubicRegressions
open Fisher MultiGraph

/-- Three parallel original occurrences with one source and one target vertex. -/
def triplePorts : (Bool × Fin 3) ≃ (Fin 3 × Bool) := Equiv.prodComm _ _

example (e : Fin 3) : (cubicOriginal triplePorts).src e = false := rfl
example (e : Fin 3) : (cubicOriginal triplePorts).dst e = true := rfl

/-- All real weights, including zero, instantiate the proved matching identity. -/
example (x : Fin 3 → ℝ) :
    (cubicOriginal triplePorts).evenSubgraphSum x =
      (cubicDecoration triplePorts).perfectMatchingSum
        (cubicPolynomialWeight triplePorts x) := cubic_fisher_polynomial _ _

/-- Internal triangle edges really carry signed polynomial weights. -/
example : cubicPolynomialWeight triplePorts ![(-2 : ℝ), 3, 0] (Sum.inr (false, 2)) = -6 := by
  change (-2 : ℝ) * 3 = -6
  norm_num

/-- A zero factor is preserved exactly, with no reciprocal operation. -/
example : cubicPolynomialWeight triplePorts ![(-2 : ℝ), 3, 0] (Sum.inr (false, 0)) = 0 := by
  change (3 : ℝ) * 0 = 0
  norm_num

/-- The unique internal choice for no selected original edges is empty. -/
example : triangleCompletion (Finset.univ : Finset (Fin 3)) = ∅ := by
  simp [triangleCompletion]

/-- Two selected original ports force the single opposite internal triangle edge. -/
example : triangleCompletion ({2} : Finset (Fin 3)) = {2} := by
  simp [triangleCompletion]

end PlanarHom.FisherCubicRegressions
