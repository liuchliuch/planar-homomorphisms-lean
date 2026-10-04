import PlanarHom.TypedMixedPhysicalAvailability

/-! Boundary regressions for actual mixed source availability. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext.MixedRegressions
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral RectangularMixedGadgets TypedGadgetAppend

private def policies : Fin 3→Fin 2→Fin 2→Prop := ![crossPolicy,sameX,sameY]

/-- Unequal sides: a source cross label and a Y matrix in the same contextual
family suffice; no Y identity or foreign closure record is assumed. -/
example (F : Fin 3→Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j))
    (B : Matrix (Fin 2) (Fin 3) ℝ) (hB : F 0=crossFin B)
    (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K∈yFamily F policies) :
    B*K*B.transpose∈xFamily F policies :=
  mixedThree_from_generator_mem_xFamily F policies hF 0 B hB rfl K hK

example (F : Fin 3→Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j))
    (B : Matrix (Fin 2) (Fin 3) ℝ) (hB : F 0=crossFin B)
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K∈xFamily F policies) :
    entrySquare (K*B)*(entrySquare (K*B)).transpose∈xFamily F policies :=
  mixedDiamond_from_generator_mem_xFamily F policies hF 0 B hB rfl K hK

/-- Extract the actual append-to-original reduction in an arbitrary retained
context. Its binary labels, unaries, U/T permissions and source basis survive. -/
def mixedDiamondWithRetainedContext {bt ut : ℕ}
    (F : Fin 3→Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j))
    (B : Matrix (Fin 2) (Fin 3) ℝ) (hB : F 0=crossFin B)
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K∈xFamily F policies)
    (L : RealLanguage (2+3) bt ut) (BL : Fin bt→Fin 2→Fin 2→Prop)
    (T : Fin ut→Fin 2→Prop) (hunit : ∀i,L.weights i=1)
    (hcontains : L.ContainsTypedMatrices BL F policies) :=
  (mixedDiamond_from_generator_mem_xFamily F policies hF 0 B hB rfl K hK).2.reduction
    L BL T hunit hcontains

/-- No nonempty-side hypothesis leaks into physical value or source membership. -/
example (F : Fin 3→Matrix (Fin (0+3)) (Fin (0+3)) ℝ)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j))
    (B : Matrix (Fin 0) (Fin 3) ℝ) (hB : F 0=crossFin B)
    (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K∈yFamily F policies) :
    B*K*B.transpose∈xFamily (x:=0) (y:=3) F policies :=
  mixedThree_from_generator_mem_xFamily F policies hF 0 B hB rfl K hK

example : mixedThreeTag=(fun _=>1) := rfl
example : mixedDiamondTag=![0,0,1,0,0] := by
  funext k
  fin_cases k <;> rfl

/-- The first diamond occurrence is genuinely XX, so this gadget cannot be
misidentified as an all-cross bipartite template. -/
example : label 0=0 ∧ sameX 0 0 ∧ ¬crossPolicy 0 0 := by
  simp [label,sameX,crossPolicy]

example (B : Matrix (Fin 2) (Fin 3) ℝ) (K : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 2) :
    coloredDomainInteraction mixedThreePath mixedThreeLabel mixedThreeTag
      ![onYFin K,crossFin B] (domains 2 3) (leftEmbedding i) (leftEmbedding i)=
      (B*K*B.transpose) i i := by
  rw [mixedThree_physical_value,zeroExtendFin_left]

end PlanarHom.TypedBipartiteContext.MixedRegressions
