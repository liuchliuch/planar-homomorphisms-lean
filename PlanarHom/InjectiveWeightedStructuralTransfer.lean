import PlanarHom.CenteredLogStructuralForm

/-! Reusable exact passage from an injective original row system to its
canonical actual-row quotient. -/
noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C:Type}

theorem AllowedWeightedBlock.weightedClass [Nonempty C] {M:Matrix C C ℝ} {w:C→ℝ}
    (h:AllowedWeightedBlock M w) : WeightedClass M w := by
  refine ⟨1,fun _=>0,?_,?_,?_⟩
  · intro r; exact ⟨Classical.choice inferInstance,Subsingleton.elim _ _⟩
  · intro i j h; exact (h rfl).elim
  · intro r
    let e:{c:C//(0:Fin 1)=r}≃C := {
      toFun:=Subtype.val
      invFun:=fun c=>⟨c,Subsingleton.elim _ _⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
    exact h.equiv e

theorem actual_membership_of_weightedClass [Fintype C]
    (M:Matrix C C ℝ) (w:C→ℝ) (hs:∀i j,M i j=M j i)
    (hrows:Function.Injective M) (h:WeightedClass M w) : PositiveVertexWeightClass M w hs := by
  apply WeightedClass.of_equiv (CenteredLogStructural.actualRowEquiv M hrows)
  change WeightedClass M (fun i=>Twins.quotientWeight M w (Quotient.mk _ i))
  have hw:(fun i=>Twins.quotientWeight M w (Quotient.mk _ i))=w := by
    funext i; exact CenteredLogStructural.quotientWeight_of_injective M hrows w i
  rwa [hw]

end PlanarHom.Structures
