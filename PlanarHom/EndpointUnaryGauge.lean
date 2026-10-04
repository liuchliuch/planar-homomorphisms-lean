import PlanarHom.RectangularNormalizedMomentPrograms

/-! NEW compatibility for literal endpoint decoration. The needed compiler is
the same-unary specialization; both loop incidences are retained by the proved
endpoint program. No unsupported different-unary compiler is asserted. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.EndpointUnaryGauge
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {C R : Type} [CommSemiring R]

def decorated (M : Matrix C C R) (a b : C → R) : Matrix C C R :=
  fun i j=>a i*M i j*b j

variable {K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension bt ut : ℕ}

def sameReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (old : Fin bt) (unary : Fin ut) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (decorated (M old) (U unary) (U unary))) U w)
      (evaluationProblem basis M U w) := by
  simpa only [pow_zero,mul_one] using
    EndpointUnarySource.gaugeMomentOneQueryReduction basis M U w old unary unary 0

end PlanarHom.EndpointUnaryGauge
