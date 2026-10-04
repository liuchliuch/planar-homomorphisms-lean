import PlanarHom.TypedGadgetAppendTransport
import PlanarHom.TypedGadgetAppendColoredTyping

/-! APPEND directly from an actual edge-coloured prescribed-domain gadget,
with all original binary labels and ordinary unary companions retained. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TypedGadgetAppend
open Complexity Complexity.MixedCode PrescribedDomains FixedGadgetNetwork EdgeSubstitution FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension p e bt ut dt : ℕ}

/-- The literal finite assignment sum of the domain-typed coloured gadget. -/
def coloredDomainInteraction (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (privateTag : Fin p → Fin dt)
    (M : Fin bt → Matrix C C K) (D : Fin dt → Set C) : Matrix C C K :=
  fun a b => ∑ η : Fin p → C,
    (∏ j, indicator (R:=K) (D (privateTag j)) (η j)) *
      ∏ i, M (label i) (TwoTerminal.extend a b η (G.src i))
        (TwoTerminal.extend a b η (G.dst i))

omit [Algebra ℚ K] in
theorem templateInteraction_typedColored (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (privateTag : Fin p → Fin dt)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (D : Fin dt → Set C) :
    templateInteraction (ofTypedColoredTwoTerminal G label privateTag ut) M
      (extendedUnaries U D) = coloredDomainInteraction G label privateTag M D := by
  funext a b
  have h := ofTypedColoredTwoTerminal_signature_domains G label privateTag ut M U D
    (fun d : Fin 2 => if d.val=0 then a else b)
  simpa only [templateInteraction,coloredDomainInteraction,Fin.val_zero,Fin.val_one,
    ite_true,one_ne_zero,ite_false] using h

/-- Generic typed gadget APPEND with the exact original source language and
source-domain promise. The edge contract is arbitrary and need not be cross-only. -/
def coloredAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (hedges : ∀ x y, A x y → ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis
        (appendOne M (templateInteraction (ofTypedColoredTwoTerminal G label privateTag ut)
          M (extendedUnaries U D))) U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) :=
  appendReduction basis M U D B T A fallback
    (ofTypedColoredTwoTerminal G label privateTag ut)
    (ofTypedColoredTwoTerminal_valid G label privateTag ut) rfl
    (ofTypedColoredTwoTerminal_planar G label privateTag ut hG)
    (ofTypedColoredTwoTerminal_typing_exists B A G label privateTag ut hedges)

/-- The same APPEND theorem stated with the actual finite-sum matrix. -/
def coloredAppendDomainReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (hedges : ∀ x y, A x y → ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (coloredDomainInteraction G label privateTag M D))
        U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  have h := coloredAppendReduction basis G label privateTag hG M U D B T A fallback hedges
  rw [templateInteraction_typedColored] at h
  exact h

/-- Identify the new finite-sum signature with an algebraic matrix formula
while retaining the exact original mixed-language oracle. -/
def coloredAppendReduction_of_signature (basis : Module.Basis (Fin dimension) ℚ K)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (hedges : ∀ x y, A x y → ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i)))
    (N : Matrix C C K) (hN : coloredDomainInteraction G label privateTag M D=N) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M N) U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  have h := coloredAppendDomainReduction basis G label privateTag hG M U D B T A fallback hedges
  rw [hN] at h
  exact h

/-- Agreement is needed only for actual colors in permitted endpoint domains;
this includes zero-extension for gadgets with isolated same-side terminals. -/
def coloredAppendReduction_on_domains (basis : Module.Basis (Fin dimension) ℚ K)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (hedges : ∀ x y, A x y → ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i)))
    (N : Matrix C C K)
    (hN : ∀ x y, A x y → ∀ a∈D x,∀ b∈D y,
      coloredDomainInteraction G label privateTag M D a b=N a b) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M N) U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  apply appendReduction_on_domains basis M U D B T A fallback
    (ofTypedColoredTwoTerminal G label privateTag ut)
    (ofTypedColoredTwoTerminal_valid G label privateTag ut) rfl
    (ofTypedColoredTwoTerminal_planar G label privateTag ut hG)
    (ofTypedColoredTwoTerminal_typing_exists B A G label privateTag ut hedges) N
  rw [templateInteraction_typedColored]
  exact hN

end PlanarHom.TypedGadgetAppend
