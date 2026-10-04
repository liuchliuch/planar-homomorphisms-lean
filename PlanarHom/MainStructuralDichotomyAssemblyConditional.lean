import PlanarHom.MainStructuralDichotomyTransportConditional
import PlanarHom.NonnegativeSupportShapes

/-! Internal assembly with precisely one explicit remaining rectangular source
classification argument. This is not an unconditional main theorem: the
argument is to be discharged by the separately checked rectangular theorem. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures RootedRestriction NonnegativeSupportShapes
open RectangularUnweightedSourceForms RectangularSourceNormSimulation
variable {q : ℕ}

/-- All original support components are classified using actual component
extraction programs. The only supplied theorem is the stated rectangular
source endpoint; positive and zero cases use the explicitly supplied Potts foundation. -/
theorem main_support_blocks_of_rectangular_source_of_potts
    (hPotts : PositivePottsFoundation)
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (T : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ),
      (∀ i j,0<V i j) → (∀ i j,T.matrices 0 i j=block V i j) →
      (∀ i,T.weights i=1) → ¬PromisedSharpPHard T.problem → RectangularTensorForm V)
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hnot : ¬PromisedSharpPHard L.problem) :
    ∀ c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      AllowedBlock (fun i j : c.supp=>L.matrices 0 i.val j.val) := by
  have hw : ∀ i,0<L.weights i := fun i=>by rw [hunit]; exact zero_lt_one
  intro c
  let S := L.supportFiniteLanguage c.supp
  let e0 := (Fintype.equivFin c.supp).symm
  have red := L.supportFiniteReduction hs hw c.supp (component_colorClosed _ hs c)
  have hnS : ¬PromisedSharpPHard S.problem := fun hh=>hnot (hh.trans red)
  have hc := L.nonnegative_support_shapes_of_not_hard hPotts hs hnn hw hnot c
  cases hc with
  | zero e hm => exact .zero e (fun i j=>congrFun (congrFun hm i) j)
  | positive hp =>
    letI : Nonempty c.supp := c.nonempty_supp.to_subtype
    letI : Nonempty (Fin (Fintype.card c.supp)) := ⟨⟨0,Fintype.card_pos⟩⟩
    have hb := S.main_positive_block_of_not_hard_of_potts hPotts (fun i=>hunit _)
      (fun i j=>hs _ _) (fun i j=>hp _ _) hnS
    exact AllowedBlock.of_equiv e0 hb
  | bipartite p s hp hspos e V hV hM =>
    letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
    letI : Nonempty (Fin s) := ⟨⟨0,hspos⟩⟩
    let g : Fin (p+s)≃c.supp := finSumFinEquiv.symm.trans e.symm
    let f : Fin (p+s)≃Fin (Fintype.card c.supp) := g.trans (Fintype.equivFin c.supp)
    let T := S.mainColorLanguage f
    have hT : T.matrices 0=(fun i j=>L.matrices 0 (g i).val (g j).val) := by
      funext i j
      simp only [T,mainColorLanguage,S,supportFiniteLanguage,f,Equiv.trans_apply,
        Equiv.symm_apply_apply]
    have hTV : ∀ i j,T.matrices 0 i j=block V i j := by
      intro i j
      rw [hT]
      have hh := congrFun (congrFun hM (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
      exact hh.trans (double_finSum V i j)
    have huT : ∀ i,T.weights i=1 := fun i=>hunit _
    have hnT : ¬PromisedSharpPHard T.problem :=
      fun hh=>hnS (hh.trans (S.mainColorSourceReduction f))
    have hf := hrect T V hV hTV huT hnT
    have hb := allowedBlock_of_form V hf
    have heq : block V=T.matrices 0 := (funext (fun i=>funext (hTV i))).symm
    rw [heq,hT] at hb
    exact AllowedBlock.of_equiv g hb

/-- The source nonnegative class, assembled without discarding zero rows,
repeated rows, disconnected support, or any original graph input. -/
theorem main_nonnegative_class_of_rectangular_source_of_potts
    (hPotts : PositivePottsFoundation)
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (T : RealLanguage (p+s) 1 0) (V : Matrix (Fin p) (Fin s) ℝ),
      (∀ i j,0<V i j) → (∀ i j,T.matrices 0 i j=block V i j) →
      (∀ i,T.weights i=1) → ¬PromisedSharpPHard T.problem → RectangularTensorForm V)
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hnot : ¬PromisedSharpPHard L.problem) :
    NonnegativeClass (L.matrices 0) :=
  nonnegativeClass_of_supportBlocks _ hs
    (L.main_support_blocks_of_rectangular_source_of_potts hPotts hrect hunit hs hnn hnot)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
