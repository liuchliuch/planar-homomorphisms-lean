import PlanarHom.DomainDistanceKernelAvailability

/-! Source-facing real-algebraic prescribed-domain uniform distance kernels.
The selected source matrix is global on its ambient color set; all narrower
old vertex domains and companion permissions remain exactly the original ones. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains LogarithmicSupport
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

def domainDistanceKernelTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) (old : Fin bt) :
    PromiseProblem := DomainDistanceKernelAvailability.targetProblem L.basis L.matricesK L.unariesK D B T old

/-- Explicit extension to an arbitrary endpoint-policy table satisfying exactly
the required internal-full-domain path cases. -/
def lemma42_domain_of_pathTyping (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hH : (L.matrices old).PosDef) (hconn : (logSupport (L.matrices old)).Connected)
    (hpositive : ∀ i j, (logSupport (L.matrices old)).Adj i j →
      0 < EntropyCompletion.matrixLog (L.matrices old) i j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainDistanceKernelTargetProblem D B T old) base := by
  apply (DomainDistanceKernelAvailability.reduction_of_pathTyping L.basis L.matricesK L.unariesK
    D B T old full hfull hpath hH hconn hpositive).trans
  simpa only [RealLanguage.domainProblem,weightsK_eq_one L hunit] using available

/-- Canonical global-C source scope, including old vertices with narrower domains.
No new endpoint-policy permission is introduced by the reduction. -/
def lemma42_global_domain (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hH : (L.matrices old).PosDef) (hconn : (logSupport (L.matrices old)).Connected)
    (hpositive : ∀ i j, (logSupport (L.matrices old)).Adj i j →
      0 < EntropyCompletion.matrixLog (L.matrices old) i j)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainDistanceKernelTargetProblem D (withGlobalMatrix B old) T old) base :=
  L.lemma42_domain_of_pathTyping hunit D (withGlobalMatrix B old) T old full hfull
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y) hH hconn hpositive base available

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
