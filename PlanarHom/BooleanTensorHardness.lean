import PlanarHom.BooleanTensorSourceAssembly
import PlanarHom.BiasedBooleanFoundationClosed

/-! NEW unconditional hard branch of source Theorem 5.1. The independent biased
Boolean foundation is now discharged by the actual signed-NAND planar compiler,
source-loop unary access, prime normalization and exact product interpolation. -/
noncomputable section
namespace PlanarHom.BooleanUnequalFactorReduction
open Complexity AlgebraicProductInterpolation
variable {q bt ut d:ℕ}

theorem scaled_tensor_promisedSharpPHard (L:RealLanguage q bt ut)
    (hunit:∀i,L.weights i=1) (old:Fin bt) (e:Fin q≃Boolean.Cube d)
    (F:Fin d→Matrix Bool Bool ℝ) (hF:∀i,(F i).PosDef)
    (hpos:∀i j k,0<F i j k) (halg:∀i j k,IsAlgebraic ℚ (F i j k))
    (γ:ℝ) (hγ:0<γ) (hγalg:IsAlgebraic ℚ γ)
    (hsource:Matrix.reindex e e (L.matrices old)=γ • CubeTensorExponential.tensor F)
    (hbias:∃i,F i false false≠F i true true):PromisedSharpPHard L.problem:=
  BooleanTensorSourceAssembly.scaled_tensor_hard_of_foundation
    BiasedPositiveHardness.biasedBooleanFoundation L hunit old e F hF hpos halg γ hγ hγalg hsource hbias

theorem tensor_promisedSharpPHard (L:RealLanguage q bt ut)
    (hunit:∀i,L.weights i=1) (old:Fin bt) (e:Fin q≃Boolean.Cube d)
    (F:Fin d→Matrix Bool Bool ℝ) (hF:∀i,(F i).PosDef)
    (hpos:∀i j k,0<F i j k) (halg:∀i j k,IsAlgebraic ℚ (F i j k))
    (hsource:Matrix.reindex e e (L.matrices old)=CubeTensorExponential.tensor F)
    (hbias:∃i,F i false false≠F i true true):PromisedSharpPHard L.problem:=
  scaled_tensor_promisedSharpPHard L hunit old e F hF hpos halg 1 (by norm_num) isAlgebraic_one
    (by simpa only [one_smul] using hsource) hbias

end PlanarHom.BooleanUnequalFactorReduction
