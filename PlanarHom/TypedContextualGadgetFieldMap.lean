import PlanarHom.TypedContextualGadgetSemantics
import PlanarHom.MixedEvaluationFieldMap

/-! Exact coefficient-field transport for actual prescribed-domain gadget sums.
Every private vertex retains its intrinsic domain under the field map. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.TypedGadgetAppend
open PrescribedDomains

/-- Ring maps commute with the literal typed gadget sum, preserving the domains. -/
theorem map_coloredDomainInteraction {C K L : Type} [Fintype C] [Field K] [Field L]
    {p e bt dt : ℕ} (φ : K →+* L) (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (tag : Fin p→Fin dt)
    (M : Fin bt→Matrix C C K) (D : Fin dt→Set C) (a b : C) :
    φ (coloredDomainInteraction G label tag M D a b)=
      coloredDomainInteraction G label tag (fun l i j=>φ (M l i j)) D a b := by
  simp only [coloredDomainInteraction,map_sum,map_mul,map_prod,map_indicator]

end PlanarHom.TypedGadgetAppend

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open TypedGadgetAppend
variable {q bt ut p e dt : ℕ}

/-- Literal real matrix of the gadget with every prescribed private domain. -/
def typedColoredGadgetMatrix (L : RealLanguage q bt ut)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (tag : Fin p→Fin dt) (D : Fin dt→Set (Fin q)) : Matrix (Fin q) (Fin q) ℝ :=
  coloredDomainInteraction G label tag L.matrices D

/-- The same finite sum in the source language's canonical number field. -/
def typedColoredGadgetMatrixK (L : RealLanguage q bt ut)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (tag : Fin p→Fin dt) (D : Fin dt→Set (Fin q)) : Matrix (Fin q) (Fin q) L.field :=
  coloredDomainInteraction G label tag L.matricesK D

theorem typedColoredGadgetMatrixK_coe (L : RealLanguage q bt ut)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (tag : Fin p→Fin dt) (D : Fin dt→Set (Fin q)) (i j : Fin q) :
    (L.typedColoredGadgetMatrixK G label tag D i j:ℝ)=
      L.typedColoredGadgetMatrix G label tag D i j := by
  simpa only [typedColoredGadgetMatrixK,typedColoredGadgetMatrix,matricesK_coe] using
    map_coloredDomainInteraction L.field.val.toRingHom G label tag L.matricesK D i j

theorem typedColoredGadgetMatrix_algebraic (L : RealLanguage q bt ut)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (tag : Fin p→Fin dt) (D : Fin dt→Set (Fin q)) (i j : Fin q) :
    IsAlgebraic ℚ (L.typedColoredGadgetMatrix G label tag D i j) := by
  rw [←L.typedColoredGadgetMatrixK_coe G label tag D i j]
  exact (IsAlgebraic.of_finite ℚ (L.typedColoredGadgetMatrixK G label tag D i j)).algHom L.field.val

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
