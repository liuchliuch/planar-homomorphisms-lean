import PlanarHom.TypedMixedPhysicalAvailabilityValues

/-! Source-facing availability of the literal mixed physical gadgets of §9.2.
The K matrix belongs to the same typed retained-context family as the original
cross generator B. No directed B-only closure or individual oracle reduction
is substituted for this joint contextual statement. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral RectangularMixedGadgets
variable {x y s : ℕ}

/-- The actual three-edge path with two private Y vertices enters the X family. -/
theorem mixedThree_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (B : Matrix (Fin x) (Fin y) ℝ)
    (hB : TypedContextuallyAvailable (domains x y) F FB (crossFin B) crossPolicy)
    (K : Matrix (Fin y) (Fin y) ℝ) (hK : K∈yFamily F FB) :
    B*K*B.transpose∈xFamily F FB := by
  have hA : ∀l,TypedContextuallyAvailable (domains x y) F FB
      ((![onYFin K,crossFin B] : Fin 2→Matrix _ _ ℝ) l)
      ((![sameY,crossPolicy] : Fin 2→Fin 2→Fin 2→Prop) l) := by
    intro l
    fin_cases l
    · exact hK.2
    · exact hB
  have h := typed_contextual_colored_gadget (domains x y) F FB
    ![onYFin K,crossFin B] ![sameY,crossPolicy] hA
    mixedThreePath mixedThreeLabel mixedThreeTag mixedThreePath_planar sameX 0
    mixedThreePath_edges
  rw [mixedThree_physical_value] at h
  refine ⟨?_,h⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose B hK.1

/-- The actual eight-edge double diamond enters the X family with all five
private tags checked against the original domains. -/
theorem mixedDiamond_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (B : Matrix (Fin x) (Fin y) ℝ)
    (hB : TypedContextuallyAvailable (domains x y) F FB (crossFin B) crossPolicy)
    (K : Matrix (Fin x) (Fin x) ℝ) (hK : K∈xFamily F FB) :
    entrySquare (K*B)*(entrySquare (K*B)).transpose∈xFamily F FB := by
  have hA : ∀l,TypedContextuallyAvailable (domains x y) F FB
      ((![zeroExtendFin (y:=y) K,crossFin B] : Fin 2→Matrix _ _ ℝ) l)
      ((![sameX,crossPolicy] : Fin 2→Fin 2→Fin 2→Prop) l) := by
    intro l
    fin_cases l
    · exact hK.2
    · exact hB
  have h := typed_contextual_colored_gadget (domains x y) F FB
    ![zeroExtendFin (y:=y) K,crossFin B] ![sameX,crossPolicy] hA
    doubleDiamond label mixedDiamondTag doubleDiamond_planarEdgeGadget sameX 0
    mixedDiamond_edges
  have hs : K.transpose=K := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.1.eq
  rw [mixedDiamond_physical_value B K hs] at h
  refine ⟨?_,h⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self (entrySquare (K*B))

/-- Source-generator form: B is literally one of the original typed labels,
and K is available in that same contextually quantified family. -/
theorem mixedThree_from_generator_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : F old=crossFin B) (hpolicy : FB old=crossPolicy)
    (K : Matrix (Fin y) (Fin y) ℝ) (hK : K∈yFamily F FB) :
    B*K*B.transpose∈xFamily F FB := by
  have hg := typed_contextual_generator (domains x y) F FB hF old
  rw [hB,hpolicy] at hg
  exact mixedThree_mem_xFamily F FB B hg K hK

/-- Source-generator form for the physical parallel-square Gram. -/
theorem mixedDiamond_from_generator_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : F old=crossFin B) (hpolicy : FB old=crossPolicy)
    (K : Matrix (Fin x) (Fin x) ℝ) (hK : K∈xFamily F FB) :
    entrySquare (K*B)*(entrySquare (K*B)).transpose∈xFamily F FB := by
  have hg := typed_contextual_generator (domains x y) F FB hF old
  rw [hB,hpolicy] at hg
  exact mixedDiamond_mem_xFamily F FB B hg K hK

end PlanarHom.TypedBipartiteContext
