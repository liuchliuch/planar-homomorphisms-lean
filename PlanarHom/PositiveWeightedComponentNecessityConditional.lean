import PlanarHom.PositiveWeightedSourceNecessity
import PlanarHom.MainSourceQuotientFacts

/-! Positive-component necessity with an explicit Potts foundation premise;
closed-row and finite-support source helpers are imported from compiled files. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity RootedRestriction
variable {q : ℕ}

theorem positive_component_weighted_block_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hinj : Function.Injective (L.matrices 0)) (hw : ∀ i,0<L.weights i)
    (c : (colorSupport (L.matrices 0) hs).ConnectedComponent)
    (hp : ∀ i j : c.supp,0<L.matrices 0 i.val j.val)
    (hnot : ¬PromisedSharpPHard L.problem) :
    Structures.AllowedWeightedBlock (fun i j : c.supp=>L.matrices 0 i.val j.val)
      (fun i : c.supp=>L.weights i.val) := by
  letI : Nonempty c.supp := c.nonempty_supp.to_subtype
  letI : Nonempty (Fin (Fintype.card c.supp)) := ⟨⟨0,Fintype.card_pos⟩⟩
  let S := L.supportFiniteLanguage c.supp
  let e := (Fintype.equivFin c.supp).symm
  have hclosed := component_colorClosed (L.matrices 0) hs c
  have hrows := closed_rows_injective (L.matrices 0) hinj c.supp hclosed
  have hiS : Function.Injective (S.matrices 0) := by
    intro i j he
    apply e.injective
    apply hrows
    funext k
    have h := congrFun he (e.symm k)
    change L.matrices 0 (e i).val (e (e.symm k)).val=L.matrices 0 (e j).val (e (e.symm k)).val at h
    rw [e.apply_symm_apply] at h
    exact h
  have red := L.supportFiniteReduction hs hw c.supp hclosed
  have hb := S.positive_weighted_block_of_not_hard hPotts 0 (fun i j=>hs _ _)
    (fun i j=>hp _ _) hiS (fun i=>hw _) (fun h=>hnot (h.trans red))
  exact Structures.AllowedWeightedBlock.of_equiv e hb

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
