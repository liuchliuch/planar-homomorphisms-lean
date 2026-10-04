import PlanarHom.FixedRealZeroWeightDeletion
import PlanarHom.VertexMomentUnarySource

/-! NEW: executable endpoint gauges and all-vertex moments with represented
fixed-real outputs. Loops receive both endpoint occurrences; isolated vertices
receive their moment occurrences. Every old label and background is retained. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealGaugeMoments
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit
open FiniteLanguageAliases EndpointUnarySource
variable {d e b u : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction d) K] [Fintype C]
variable (basis : Module.Basis (Fin e) (RationalFunction d) K)

def endpointReduction (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (old : Fin b) (gauge : Fin u) :
    Reduction (FixedRealComponents.problem basis (appendOne M (unaryGauge (M old) (U gauge))) U w)
      (FixedRealComponents.problem basis M U w) := by
  apply queryReduction (FixedRealExtension.presentation basis) MixedCode.encoding MixedCode.encoding
    MixedCode.normalizer (PlanarValid (b+1) u) (PlanarValid b u)
    (totalEvaluation (appendOne M (unaryGauge (M old) (U gauge))) U w) (totalEvaluation M U w)
    (endpointTransform old gauge) (fp_endpointTransform old gauge) (endpointTransform_planar old gauge)
  intro g hg
  rw [totalEvaluation_valid _ _ _ _ (endpointTransform_planar old gauge g hg).1,
    totalEvaluation_valid _ _ _ g hg.1]
  exact evaluate_endpointTransform old gauge g hg.1 M U w _

def momentReduction (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (selected : Fin u) (power : ℕ) :
    Reduction (FixedRealComponents.problem basis M U (fun i => w i * (U selected i)^power))
      (FixedRealComponents.problem basis M U w) := by
  apply queryReduction (FixedRealExtension.presentation basis) MixedCode.encoding MixedCode.encoding
    MixedCode.normalizer (PlanarValid b u) (PlanarValid b u)
    (totalEvaluation M U (fun i => w i * (U selected i)^power)) (totalEvaluation M U w)
    (momentTransform selected power) (fp_momentTransform selected power) (momentTransform_planar selected power)
  intro g hg
  rw [totalEvaluation_valid _ _ _ _ (momentTransform_planar selected power g hg).1,
    totalEvaluation_valid _ _ _ g hg.1]
  exact evaluate_momentTransform selected power g hg.1 M U w _

def gaugeMomentReduction (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (old : Fin b) (gauge moment : Fin u) (power : ℕ) :
    Reduction (FixedRealComponents.problem basis (appendOne M (unaryGauge (M old) (U gauge))) U
      (fun i => w i * (U moment i)^power)) (FixedRealComponents.problem basis M U w) := by
  apply queryReduction (FixedRealExtension.presentation basis) MixedCode.encoding MixedCode.encoding
    MixedCode.normalizer (PlanarValid (b+1) u) (PlanarValid b u)
    (totalEvaluation (appendOne M (unaryGauge (M old) (U gauge))) U (fun i => w i * (U moment i)^power))
    (totalEvaluation M U w) (gaugeMomentTransform old gauge moment power)
    (fp_gaugeMomentTransform old gauge moment power) (gaugeMomentTransform_planar old gauge moment power)
  intro g hg
  rw [totalEvaluation_valid _ _ _ _ (gaugeMomentTransform_planar old gauge moment power g hg).1,
    totalEvaluation_valid _ _ _ g hg.1]
  exact evaluate_gaugeMomentTransform old gauge moment power g hg.1 M U w _

end PlanarHom.FixedRealGaugeMoments
