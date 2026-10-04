import PlanarHom.TypedGadgetAppend
import PlanarHom.TypedBipartiteSpectralTransport

/-! A typed APPEND observes only the allowed endpoint-domain entries.
Entries outside the prescribed policy can therefore be completed arbitrarily,
including zero-extension of same-side gadgets with isolated terminals. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open Complexity Complexity.MixedCode PrescribedDomains FixedGadgetNetwork EdgeSubstitution
open FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension bt ut dt : ℕ}

/-- The same concrete caller compiles any matrix agreeing with the genuine
finite gadget signature at the actual permitted endpoint domains. No pinning
oracle, support assumption, or non-isolated-terminal assumption is introduced. -/
def appendReduction_on_domains (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop)
    (fallback : Fin dt) (t : Template) (ht : t.code.Valid bt (ut+dt)) (hb : t.boundary=2)
    (hp : TwoTerminal.PlanarEdgeGadget (t.edgeGadget hb ht))
    (hnew : ∀x y,A x y → ∃tag,TemplateTyping (ut:=ut) B t tag ∧ tag 0=x ∧ tag 1=y)
    (N : Matrix C C K)
    (hN : ∀x y,A x y → ∀i∈D x,∀j∈D y,templateInteraction t M (extendedUnaries U D) i j=N i j) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M N) U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let r := appendReduction basis M U D B T A fallback t ht hb hp hnew
  refine r.transport _ _ (fun _ h=>h) (fun _ h=>h) ?_ (fun _ _=>rfl)
  intro raw hr
  apply TypedBipartiteSpectral.domain_value_congr basis _ _ U (fun _=>1) D (appendOne B A) T ?_ raw hr
  intro l
  refine Fin.addCases (fun l x y h i hi j hj=>?_) (fun l x y h i hi j hj=>?_) l
  · simp only [appendOne,Fin.addCases_left]
  · simp only [appendOne,Fin.addCases_right] at h ⊢
    exact (hN x y h i hi j hj).symm

/-- Convenient exact-signature specialization, using the original source
basis throughout even when the displayed target matrix has a separate name. -/
def appendReduction_of_signature (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop)
    (fallback : Fin dt) (t : Template) (ht : t.code.Valid bt (ut+dt)) (hb : t.boundary=2)
    (hp : TwoTerminal.PlanarEdgeGadget (t.edgeGadget hb ht))
    (hnew : ∀x y,A x y → ∃tag,TemplateTyping (ut:=ut) B t tag ∧ tag 0=x ∧ tag 1=y)
    (N : Matrix C C K) (hN : templateInteraction t M (extendedUnaries U D)=N) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M N) U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) :=
  appendReduction_on_domains basis M U D B T A fallback t ht hb hp hnew N
    (fun _ _ _ i _ j _=>congrArg (fun A=>A i j) hN)

end PlanarHom.TypedGadgetAppend
