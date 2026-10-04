import PlanarHom.TypedRealLanguagePresentation
import PlanarHom.TypedGadgetAppendColoredReduction

/-! Canonical-field typed colored gadget appending. The actual prescribed-domain
machine is retained, and the new matrix need agree only on permitted endpoints.
No binary or unary companion, endpoint policy, or intrinsic domain is erased. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases TypedGadgetAppend
variable {q dt bt ut p e : ℕ}

/-- Real-language wrapper around the genuine colored prescribed-domain APPEND.
The fixed-field target is realized in the original language field, so the output
has the canonical answer basis of the literal appended real language. -/
def coloredAppendRealizationReduction (L : RealLanguage q bt ut)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop)
    (T : Fin ut→Fin dt→Prop) (hunit : ∀i,L.weights i=1)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (privateTag : Fin p→Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (NB : Fin dt→Fin dt→Prop) (fallback : Fin dt)
    (hedges : ∀a b,NB a b→∀k,B (label k)
      (TwoTerminal.extend a b privateTag (G.src k))
      (TwoTerminal.extend a b privateTag (G.dst k)))
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (NK : Matrix (Fin q) (Fin q) L.field) (hNK : ∀i j,(NK i j:ℝ)=N i j)
    (hdomains : ∀a b,NB a b→∀i∈D a,∀j∈D b,
      coloredDomainInteraction G label privateTag L.matricesK D i j=NK i j) :
    PromisePolyTimeTuringReduction
      ((L.appendBinary N hN).typedProblem D (appendOne B NB) T)
      (L.typedProblem D B T) := by
  have hw : L.weightsK=fun _=>1 := by
    funext i
    exact Subtype.ext (hunit i)
  have present := L.typedAppendBinaryRealizationReduction D B T NB N hN L.field L.basis
    L.matricesK L.unariesK L.weightsK NK
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl) hNK
  have operation := coloredAppendReduction_on_domains L.basis G label privateTag hG
    L.matricesK L.unariesK D B T NB fallback hedges NK hdomains
  rw [hw] at present
  exact present.trans (by simpa only [typedProblem,hw] using operation)

end PlanarHom.TypedBipartiteContext
