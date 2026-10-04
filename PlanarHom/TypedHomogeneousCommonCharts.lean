import PlanarHom.TypedSideCommonChartSeed
import PlanarHom.AvailableClosedFamilyCube

/-! NEW conditional common X/Y charts for the actual homogeneous original
source. The all-size Potts premise is explicit; source access and all family
closure operations come from their genuine contextual compilers. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily TypedSideSourceAccess
variable {x y s : ℕ}

theorem yFamily_algebraicSourceClosed
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop) :
    AlgebraicSourceClosed (yFamily F FB) := by
  rw [yFamily_eq_swapped_xFamily]
  exact xFamily_algebraicSourceClosed _ _

theorem yFamily_effectiveClosed
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop) :
    EffectiveSpectralClosed (yFamily F FB) := by
  rw [yFamily_eq_swapped_xFamily]
  exact xFamily_effectiveClosed _ _

theorem yFamily_mixedPlanarGadgetClosed
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop) :
    MixedPlanarGadgetClosed (yFamily F FB) := by
  rw [yFamily_eq_swapped_xFamily]
  exact xFamily_mixedPlanarGadgetClosed _ _

theorem crossGram_from_generator_mem_yFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hFalg : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (B : Matrix (Fin x) (Fin y) ℝ) (hsource : F old=crossFin B) (hpolicy : FB old=crossPolicy) :
    B.transpose*B∈yFamily F FB := by
  rw [yFamily_eq_swapped_xFamily]
  let SF:=fun l i j=>F l (swapColors x y i) (swapColors x y j)
  let SP:=fun l a b=>FB l (swapDomains a) (swapDomains b)
  have hm : SF old=crossFin B.transpose := by
    dsimp [SF]
    rw [hsource]
    exact swap_crossFin B
  have hp : SP old=crossPolicy := by
    dsimp [SP]
    rw [hpolicy]
    exact swapDomains_crossPolicy
  simpa only [Matrix.transpose_transpose] using
    crossGram_from_generator_mem_xFamily SF SP (fun l i j=>hFalg l _ _) old B.transpose hm hp

theorem common_x_chart_from_homogeneous_generator_of_potts [Nonempty (Fin x)] [Nonempty (Fin y)]
    (hPotts : PositivePottsFoundation)
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hFalg : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀i,L.weights i=1)
    (hF : L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) F FB)
    (hcross : FixedRealRootRestrictions.Bipartite.Crosses L.matrices (ambientSide x y))
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀i j,0<B i j)
    (hproj : ∀i j,i≠j→∀t:ℝ,B i≠t•B j)
    (hsource : F old=crossFin B) (hpolicy : FB old=crossPolicy)
    (hnot : ¬PromisedSharpPHard L.problem) : Nonempty (CommonCubeChart (xFamily F FB)) := by
  have hbase:=xFamily_originalHomogeneousFiniteJointSource F FB L hunit hF hcross
  apply exists_common_cube_chart hPotts (xFamily F FB) (xFamily_algebraicSourceClosed F FB)
    (xFamily_effectiveClosed F FB) (xFamily_mixedPlanarGadgetClosed F FB) L.problem
  · intro N hN
    exact hbase 1 (fun _=>N) (fun _=>hN)
  · exact ⟨rowGramPower B,rowGramPower_admissible F FB B hB hproj
      (crossGram_from_generator_mem_xFamily F FB hFalg old B hsource hpolicy)⟩
  · exact hnot

theorem common_y_chart_from_homogeneous_generator_of_potts [Nonempty (Fin x)] [Nonempty (Fin y)]
    (hPotts : PositivePottsFoundation)
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hFalg : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀i,L.weights i=1)
    (hF : L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) F FB)
    (hcross : FixedRealRootRestrictions.Bipartite.Crosses L.matrices (ambientSide x y))
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀i j,0<B i j)
    (hproj : ∀i j,i≠j→∀t:ℝ,B.transpose i≠t•B.transpose j)
    (hsource : F old=crossFin B) (hpolicy : FB old=crossPolicy)
    (hnot : ¬PromisedSharpPHard L.problem) : Nonempty (CommonCubeChart (yFamily F FB)) := by
  have hbase:=yFamily_originalHomogeneousFiniteJointSource F FB L hunit hF hcross
  have hg:=crossGram_from_generator_mem_yFamily F FB hFalg old B hsource hpolicy
  have hadm : Admissible (yFamily F FB) (rowGramPower B.transpose) := by
    rw [yFamily_eq_swapped_xFamily] at hg ⊢
    apply rowGramPower_admissible _ _ B.transpose (fun i j=>hB j i) hproj
    simpa only [Matrix.transpose_transpose] using hg
  apply exists_common_cube_chart hPotts (yFamily F FB) (yFamily_algebraicSourceClosed F FB)
    (yFamily_effectiveClosed F FB) (yFamily_mixedPlanarGadgetClosed F FB) L.problem
  · intro N hN
    exact hbase 1 (fun _=>N) (fun _=>hN)
  · exact ⟨rowGramPower B.transpose,hadm⟩
  · exact hnot

end PlanarHom.TypedBipartiteContext
