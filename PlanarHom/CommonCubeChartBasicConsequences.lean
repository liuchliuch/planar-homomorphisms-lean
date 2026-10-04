import PlanarHom.CommonCubeChartDefinition
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport Boolean CubeTensorExponential
variable {q : ℕ}
namespace CommonCubeChart
variable {S : Set (Matrix (Fin q) (Fin q) ℝ)} (W : CommonCubeChart S)
theorem cardinality : q=2^W.dimension := by
  simpa [Boolean.Cube,Fintype.card_fun] using Fintype.card_congr W.graphIso.toEquiv
theorem nonnegative_factors (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (hgadget : MixedPlanarGadgetClosed S)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : N∈S) (hpd : N.PosDef) (hnn : ∀ i j,0≤N i j) :
    ∃ γ : ℝ,∃ A : Fin W.dimension→Matrix Bool Bool ℝ,
      0<γ ∧ IsAlgebraic ℚ γ ∧
      (∀ r,(A r).PosDef ∧ (∀ i j,0≤A r i j) ∧ (∀ i j,IsAlgebraic ℚ (A r i j))) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • CubeTensorExponential.tensor A := by
  obtain ⟨he,hγ,hγalg,hf,_⟩ := proposition48 S hA htransfer hgadget W.maximum W.admissible
    W.isMaximum W.positive_log W.graphIso N hN hpd hnn
  refine ⟨N (W.graphIso.symm zeroColor) (W.graphIso.symm zeroColor),
    factorInCoordinates W.graphIso.toEquiv N,hγ,hγalg,fun r=>⟨(hf r).1,(hf r).2.1,(hf r).2.2.1⟩,?_⟩
  ext x y
  simpa [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,
    CubeTensorExponential.tensor] using he (W.graphIso.symm x) (W.graphIso.symm y)
end CommonCubeChart
end PlanarHom.ClosedMatrixFamily
