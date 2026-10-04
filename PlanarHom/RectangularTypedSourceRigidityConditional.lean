-- NEW conditional source assembly adapted from the recovered consumer.
-- Explicit classifier hypotheses are retained for reuse by the closed assembly.
import PlanarHom.TypedHomogeneousCommonCharts
import PlanarHom.TypedMixedPhysicalAvailability
import PlanarHom.AvailableCommonCubeChart
import PlanarHom.RectangularCommonChartRigidity
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily TypedSideSourceAccess
variable {x y s bt : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
omit [Nonempty (Fin x)] [Nonempty (Fin y)] in
theorem yFamily_entrywise_pow
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (H : Matrix (Fin y) (Fin y) ℝ) (hH : H∈yFamily F FB) (n : ℕ) (hn : 0<n) :
    (fun i j=>H i j^n)∈yFamily F FB := by
  rw [yFamily_eq_swapped_xFamily] at hH ⊢
  exact xFamily_entrywise_pow _ _ H hH n hn
theorem columnGramPower_admissible
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j)
    (hgram : B.transpose*B∈yFamily F FB) :
    Admissible (yFamily F FB) (rowGramPower B.transpose) := by
  have hp := rowGramPower_posDef B.transpose (fun i j=>hB j i) hproj
  have hpos := rowGramPower_positive B.transpose (fun i j=>hB j i)
  refine ⟨?_,fun i j=>(hpos i j).le,hp,support_connected_of_positive_entries _ hp.1 hpos⟩
  simpa only [rowGramPower,Matrix.transpose_transpose] using
    yFamily_entrywise_pow F FB _ hgram _ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
theorem rectangular_tensor_of_homogeneous_source_of_potts
    (hPotts : PositivePottsFoundation)
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hFalg : ∀ l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (hF : L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) F FB)
    (hcross : FixedRealRootRestrictions.Bipartite.Crosses L.matrices (ambientSide x y))
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hrows : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hcols : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j)
    (hsource : F old=crossFin B) (hpolicy : FB old=crossPolicy)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ,∃ eX : Fin x≃Boolean.Cube d,∃ eY : Fin y≃Boolean.Cube d,
      ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j) := by
  obtain ⟨WX⟩ := common_x_chart_from_homogeneous_generator_of_potts hPotts F FB hFalg old L hunit hF hcross B hB hrows hsource hpolicy hnot
  obtain ⟨WY⟩ := common_y_chart_from_homogeneous_generator_of_potts hPotts F FB hFalg old L hunit hF hcross B hB hcols hsource hpolicy hnot
  have hAX := xFamily_algebraicSourceClosed F FB
  have hAY := yFamily_algebraicSourceClosed F FB
  have hEX := xFamily_effectiveClosed F FB
  have hEY := yFamily_effectiveClosed F FB
  have hGX := xFamily_mixedPlanarGadgetClosed F FB
  have hGY := yFamily_mixedPlanarGadgetClosed F FB
  have hbaseX := xFamily_originalHomogeneousFiniteJointSource F FB L hunit hF hcross
  have hbaseY := yFamily_originalHomogeneousFiniteJointSource F FB L hunit hF hcross
  have hg := typed_contextual_generator (domains x y) F FB hFalg old
  rw [hsource,hpolicy] at hg
  have hgramX := crossGram_mem_xFamily F FB B hg
  have hgramY := crossGram_from_generator_mem_yFamily F FB hFalg old B hsource hpolicy
  have hseedX := rowGramPower_admissible F FB B hB hrows hgramX
  have hseedY := columnGramPower_admissible F FB B hB hcols hgramY
  have hx := WX.connected_tensor hAX hEX hGX L.problem
    (fun N hN=>hbaseX 1 (fun _=>N) (fun _=>hN)) hnot _ hseedX
  have hy := WY.connected_tensor hAY hEY hGY L.problem
    (fun N hN=>hbaseY 1 (fun _=>N) (fun _=>hN)) hnot _ hseedY
  apply RectangularChartTransport.tensor_form_from_common_charts WX WY hAX hAY hEX hEY B hB
    (max 1 (x-1)) (max 1 (y-1)) (by omega) (by omega)
  · obtain ⟨γ,ρ,_,_,hr,he⟩ := hx
    exact ⟨γ,ρ,fun i=>⟨(hr i).1,(hr i).2.1⟩,he⟩
  · obtain ⟨γ,ρ,_,_,hr,he⟩ := hy
    refine ⟨γ,ρ,fun i=>⟨(hr i).1,(hr i).2.1⟩,?_⟩
    simpa only [rowGramPower,Matrix.transpose_transpose] using he
  · intro N hN hpos
    exact WX.positive_tensor hAX hEX hGX L.problem
      (fun H hH=>hbaseX 1 (fun _=>H) (fun _=>hH)) hnot N hN hpos
  · exact fun K hK=>mixedThree_mem_xFamily F FB B hg K hK
  · exact fun K hK=>mixedDiamond_mem_xFamily F FB B hg K hK
end PlanarHom.TypedBipartiteContext
