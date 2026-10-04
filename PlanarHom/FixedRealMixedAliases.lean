import PlanarHom.FixedRealMixedInterpolation
import PlanarHom.RepresentedQueryReduction
import PlanarHom.MixedRelabelSemantics

noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedInterpolation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit FiniteLabelLookupMachines
variable {n e q a b u:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def binaryRelabelReduction (ρ:Fin a→Fin b) (M:Fin b→Matrix (Fin q) (Fin q) K)
    (U:Fin u→Fin q→K) (w:Fin q→K) :
    Reduction (problem basis (M∘ρ) U w) (problem basis M U w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid a u) (PlanarValid b u) (totalEvaluation (M∘ρ) U w) (totalEvaluation M U w)
    (relabelBinary (finTable ρ)) (fp_relabelBinary (finTable ρ))
  · intro g hg
    exact relabelBinary_planar _ hg (lookup_finTable_lt ρ)
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1,totalEvaluation_valid _ _ _ _
      (relabelBinary_valid _ hg.1 (lookup_finTable_lt ρ))]
    exact evaluate_relabelBinary g hg.1 ρ M U w

def unaryRelabelReduction (ρ:Fin a→Fin u) (M:Fin b→Matrix (Fin q) (Fin q) K)
    (U:Fin u→Fin q→K) (w:Fin q→K) :
    Reduction (problem basis M (U∘ρ) w) (problem basis M U w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid b a) (PlanarValid b u) (totalEvaluation M (U∘ρ) w) (totalEvaluation M U w)
    (relabelUnary (finTable ρ)) (fp_relabelUnary (finTable ρ))
  · intro g hg
    exact relabelUnary_planar _ hg (lookup_finTable_lt ρ)
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1,totalEvaluation_valid _ _ _ _
      (relabelUnary_valid _ hg.1 (lookup_finTable_lt ρ))]
    exact evaluate_relabelUnary g hg.1 ρ M U w

end PlanarHom.FixedRealMixedInterpolation
