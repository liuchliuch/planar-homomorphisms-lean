import PlanarHom.MainStructuralDichotomyAssemblyConditional

/-! Internal weighted-main assembly. Its one explicit rectangular-source
argument is supplied by the final closed assembly. All support, actual-row
quotient, and source-codec steps are proved here. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures RootedRestriction NonnegativeSupportShapes
open RectangularSourceNormSimulation
variable {q : ℕ}

/-- Actual support components of an actual-row-reduced source. The rectangular
argument is applied after an explicit source program and a common color chart
for both the matrix and its original vertex weights. -/
theorem main_weighted_support_blocks_of_rectangular_source_of_potts
    (hPotts : PositivePottsFoundation)
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (T : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ),
      (∀ i j,0<V i j) → (∀ i j,T.matrices 0 i j=block V i j) →
      Function.Injective (T.matrices 0) → (∀ i,0<T.weights i) →
      ¬PromisedSharpPHard T.problem → AllowedWeightedBlock (T.matrices 0) T.weights)
    (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hinj : Function.Injective (L.matrices 0))
    (hw : ∀ i,0<L.weights i) (hnot : ¬PromisedSharpPHard L.problem) :
    ∀ c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      AllowedWeightedBlock (fun i j : c.supp=>L.matrices 0 i.val j.val)
        (fun i : c.supp=>L.weights i.val) := by
  intro c
  have hc := L.nonnegative_support_shapes_of_not_hard hPotts hs hnn hw hnot c
  cases hc with
  | zero e hm => exact .zero e (fun i j=>congrFun (congrFun hm i) j) (fun i=>hw _)
  | positive hp =>
    exact L.positive_component_weighted_block_of_not_hard hPotts hs hinj hw c hp hnot
  | bipartite p s hp hspos e V hV hM =>
    letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
    letI : Nonempty (Fin s) := ⟨⟨0,hspos⟩⟩
    let S := L.supportFiniteLanguage c.supp
    let g : Fin (p+s)≃c.supp := finSumFinEquiv.symm.trans e.symm
    let f : Fin (p+s)≃Fin (Fintype.card c.supp) := g.trans (Fintype.equivFin c.supp)
    let T := S.mainColorLanguage f
    have hT : T.matrices 0=(fun i j=>L.matrices 0 (g i).val (g j).val) := by
      funext i j
      simp only [T,mainColorLanguage,S,supportFiniteLanguage,f,Equiv.trans_apply,
        Equiv.symm_apply_apply]
    have hwT : T.weights=(fun i=>L.weights (g i).val) := by
      funext i
      simp only [T,mainColorLanguage,S,supportFiniteLanguage,f,Equiv.trans_apply,
        Equiv.symm_apply_apply]
    have hTV : ∀ i j,T.matrices 0 i j=block V i j := by
      intro i j
      rw [hT]
      have hh := congrFun (congrFun hM (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
      exact hh.trans (double_finSum V i j)
    have red := L.supportFiniteReduction hs hw c.supp (component_colorClosed _ hs c)
    have hnS : ¬PromisedSharpPHard S.problem := fun hh=>hnot (hh.trans red)
    have hnT : ¬PromisedSharpPHard T.problem :=
      fun hh=>hnS (hh.trans (S.mainColorSourceReduction f))
    have hiS := L.main_supportFinite_rows_injective hinj c.supp (component_colorClosed _ hs c)
    have hiT := S.mainColor_rows_injective f hiS
    have hb := hrect T V hV hTV hiT (fun i=>hw _) hnT
    rw [hT,hwT] at hb
    exact AllowedWeightedBlock.of_equiv g hb

/-- Whole row-reduced weighted class, assembled from the genuine numerical
support partition. Empty color sets and singleton zero blocks are retained. -/
theorem main_weighted_class_of_rectangular_source_of_potts
    (hPotts : PositivePottsFoundation)
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (T : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ),
      (∀ i j,0<V i j) → (∀ i j,T.matrices 0 i j=block V i j) →
      Function.Injective (T.matrices 0) → (∀ i,0<T.weights i) →
      ¬PromisedSharpPHard T.problem → AllowedWeightedBlock (T.matrices 0) T.weights)
    (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hinj : Function.Injective (L.matrices 0))
    (hw : ∀ i,0<L.weights i) (hnot : ¬PromisedSharpPHard L.problem) :
    WeightedClass (L.matrices 0) L.weights :=
  weightedClass_of_supportBlocks _ _ hs
    (L.main_weighted_support_blocks_of_rectangular_source_of_potts hPotts hrect hs hnn hinj hw hnot)

/-- Exact main1.3 necessity on the original source, with only the explicitly
listed rectangular source theorem left to discharge. No distinct-row,
nonzero-matrix, connected-support, or loop-free hypothesis is imposed on L. -/
theorem main_positive_vertex_weight_class_of_rectangular_source_of_potts
    (hPotts : PositivePottsFoundation)
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (T : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ),
      (∀ i j,0<V i j) → (∀ i j,T.matrices 0 i j=block V i j) →
      Function.Injective (T.matrices 0) → (∀ i,0<T.weights i) →
      ¬PromisedSharpPHard T.problem → AllowedWeightedBlock (T.matrices 0) T.weights)
    (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hw : ∀ i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) :
    PositiveVertexWeightClass (L.matrices 0) L.weights hs := by
  apply (L.fullQuotient_weighted_class_iff hs).mp
  exact (L.fullQuotientLanguage hs).main_weighted_class_of_rectangular_source_of_potts hPotts hrect
    (L.main_fullQuotient_symmetric hs) (L.main_fullQuotient_nonnegative hs hnn)
    (L.fullQuotient_injective_rows hs) (L.fullQuotient_weights_positive hs hw)
    (fun hh=>hnot (hh.trans (L.fullQuotientSourceReduction hs)))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
