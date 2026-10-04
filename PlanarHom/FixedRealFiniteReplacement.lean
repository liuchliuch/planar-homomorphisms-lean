import PlanarHom.FixedRealJointInterpolation

/-! NEW: literal represented finite replacement, with all target labels
simultaneously present and all original unary/background factors retained. -/
noncomputable section
namespace PlanarHom.FixedRealMixedInterpolation
open DensePolynomial FixedRealExtension RepresentedBit ProductCompatibility FiniteLanguageAliases
variable {n e q b u r : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

def identityReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) : Reduction (problem basis M U w) (problem basis M U w) :=
  binaryRelabelReduction basis id M U w

def finiteReplacementReduction (M : Matrix (Fin q) (Fin q) K)
    (N : Fin r → Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (hz : ∀l i j, M i j = 0 → N l i j = 0)
    (hm : ∀l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => N l p.1 p.2)) :
    Reduction (problem basis N U w) (problem basis (fun _ : Fin 1 => M) U w) := by
  have all := binaryFinite_joint basis (fun _ : Fin 1 => M) U w N (fun _ => 0) hz hm
    (problem basis (fun _ : Fin 1 => M) U w) (identityReduction basis _ U w)
  have select := binaryRelabelReduction basis (Fin.natAdd 1)
    (appendFamily (fun _ : Fin 1 => M) N) U w
  have select' : Reduction (problem basis N U w)
      (problem basis (appendFamily (fun _ : Fin 1 => M) N) U w) := by
    have he : appendFamily (fun _ : Fin 1 => M) N ∘ Fin.natAdd 1 = N :=
      funext (fun l => appendFamily_new _ _ l)
    simpa only [he] using select
  exact select'.trans all

end PlanarHom.FixedRealMixedInterpolation
