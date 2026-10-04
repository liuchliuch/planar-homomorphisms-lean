import PlanarHom.SurfaceNonnegativeTractability
import PlanarHom.SurfaceWeightedQuotientTractability
import PlanarHom.SurfaceFKTTractability

/-! NEW full fixed-orientable-genus tractable structural implications.
The public input is the supplied finite embedding; component computations
retain its actual rotations and derived homology bound. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.SurfaceStructuralTractability
open Complexity SurfaceRowEvaluation
variable {C:Type} [Fintype C] {dimension:ℕ}

theorem nonnegativeClass_inFP (ambient:ℕ) (K₀:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis:Module.Basis (Fin dimension) ℚ K₀) (M:Matrix C C K₀)
    (h:Structures.NonnegativeClass (fun i j=>(M i j:ℝ))) :
    (SurfaceRawEmbedding.evaluationProblem ambient basis (fun _:Fin 1=>M)
      (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP :=
  evaluable_inFP ambient basis _ _ _
    (SurfaceWeightedBlockTractability.nonnegativeClass_inFP_of_ising
      (SurfaceFKT.positiveIsingFoundation ambient) K₀ basis M h)

theorem positiveVertexWeightClass_inFP (ambient:ℕ) (K₀:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis:Module.Basis (Fin dimension) ℚ K₀) (M:Matrix C C K₀) (w:C→K₀)
    (hs:∀i j,(M i j:ℝ)=(M j i:ℝ))
    (h:Structures.PositiveVertexWeightClass (fun i j=>(M i j:ℝ)) (fun i=>(w i:ℝ)) hs) :
    (SurfaceRawEmbedding.evaluationProblem ambient basis (fun _:Fin 1=>M)
      (fun u:Fin 0=>u.elim0) w).InFP :=
  evaluable_inFP ambient basis _ _ _
    (SurfaceWeightedBlockTractability.positiveVertexWeightClass_inFP_of_ising
      (SurfaceFKT.positiveIsingFoundation ambient) K₀ basis M w hs h)

end PlanarHom.SurfaceStructuralTractability
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity
variable {q:ℕ} (L:RealLanguage q 1 0)

theorem surface_nonnegative_class_inFP (ambient:ℕ) (hunit:∀i,L.weights i=1)
    (h:Structures.NonnegativeClass (L.matrices 0)) :
    (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK).InFP := by
  have hm:L.matricesK=fun _:Fin 1=>L.matricesK 0:=by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim l 0)
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=by funext u;exact u.elim0
  have hw:L.weightsK=fun _=>1:=by funext i;exact Subtype.ext (hunit i)
  rw [hm,hu,hw]
  exact SurfaceStructuralTractability.nonnegativeClass_inFP ambient L.field L.basis (L.matricesK 0) h

theorem surface_positive_vertex_weight_class_inFP (ambient:ℕ)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h:Structures.PositiveVertexWeightClass (L.matrices 0) L.weights hs) :
    (SurfaceRawEmbedding.evaluationProblem ambient L.basis L.matricesK L.unariesK L.weightsK).InFP := by
  have hm:L.matricesK=fun _:Fin 1=>L.matricesK 0:=by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim l 0)
  have hu:L.unariesK=(fun u:Fin 0=>u.elim0):=by funext u;exact u.elim0
  rw [hm,hu]
  exact SurfaceStructuralTractability.positiveVertexWeightClass_inFP ambient L.field L.basis
    (L.matricesK 0) L.weightsK hs h

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
