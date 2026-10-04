import PlanarHom.SurfacePlanarHardnessLift
import PlanarHom.SurfaceStructuralTractability
import PlanarHom.MainDichotomiesClosed

/-! NEW: Corollary 12.8 for every fixed orientable ambient genus, with the
actual supplied graph/rotation/complement input and original field output.
The tractable side consumes the surface algorithms; the hard side consumes
the actual planar embedding compiler. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ} (L : RealLanguage q 1 0)

theorem corollary128_unweighted (ambient : ℕ) (hunit : ∀ i, L.weights i = 1)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i)
    (hn : ∀ i j, 0 ≤ L.matrices 0 i j) :
    (NonnegativeClass (L.matrices 0) →
      (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK).InFP) ∧
    (¬NonnegativeClass (L.matrices 0) →
      PromisedSharpPHard (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK)) := by
  refine ⟨L.surface_nonnegative_class_inFP ambient hunit,?_⟩
  intro h
  exact SurfacePlanarHardness.promisedSharpPHard ambient L.basis L.matricesK L.unariesK L.weightsK
    ((MainDichotomyScope.theorem11 L hunit hs hn).2 h)

theorem corollary128_weighted (ambient : ℕ)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i)
    (hn : ∀ i j, 0 ≤ L.matrices 0 i j) (hw : ∀ i, 0 < L.weights i) :
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs →
      (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK).InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs →
      PromisedSharpPHard (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK)) := by
  refine ⟨L.surface_positive_vertex_weight_class_inFP ambient hs,?_⟩
  intro h
  exact SurfacePlanarHardness.promisedSharpPHard ambient L.basis L.matricesK L.unariesK L.weightsK
    ((MainDichotomyScope.theorem13 L hs hn hw).2 h)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
