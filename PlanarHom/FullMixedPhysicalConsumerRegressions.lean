import PlanarHom.TypedMixedPhysicalAvailabilityGram
import PlanarHom.TypedMixedPhysicalAvailabilityRegressions
import PlanarHom.RecoveredMixedDefinitionCompatibility

/-! NEW empty-side and retained-context checks for the complete recovered physical consumers. -/
noncomputable section
namespace PlanarHom.TypedBipartiteContext.FullMixedRegressions
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral RectangularMixedGadgets TypedGadgetAppend

example {x y s : ℕ} (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (B : Matrix (Fin x) (Fin y) ℝ)
    (hB : TypedContextuallyAvailable (domains x y) F FB (crossFin B) crossPolicy) :
    B*B.transpose∈xFamily F FB := crossGram_mem_xFamily F FB B hB

example {s : ℕ} (F : Fin s→Matrix (Fin (2+0)) (Fin (2+0)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (B : Matrix (Fin 2) (Fin 0) ℝ)
    (hB : TypedContextuallyAvailable (domains 2 0) F FB (crossFin B) crossPolicy)
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K∈xFamily F FB) :
    entrySquare (K*B)*(entrySquare (K*B)).transpose∈xFamily F FB :=
  mixedDiamond_mem_xFamily F FB B hB K hK

example {s : ℕ} (F : Fin s→Matrix (Fin (0+0)) (Fin (0+0)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (B : Matrix (Fin 0) (Fin 0) ℝ)
    (hB : TypedContextuallyAvailable (domains 0 0) F FB (crossFin B) crossPolicy) :
    B*B.transpose∈xFamily F FB := crossGram_mem_xFamily F FB B hB

/-- No unwanted symmetry condition appears in the rectangular three-path value. -/
example (B : Matrix (Fin 2) (Fin 3) ℚ) (K : Matrix (Fin 3) (Fin 3) ℚ) :
    coloredDomainInteraction mixedThreePath mixedThreeLabel mixedThreeTag
      ![onYFin K,crossFin B] (domains 2 3)=zeroExtendFin (y:=3) (B*K*B.transpose) :=
  mixedThree_physical_value B K

end PlanarHom.TypedBipartiteContext.FullMixedRegressions
