import PlanarHom.PositiveColorSourcePresentation
import PlanarHom.MainDichotomyFinalAssembly
import PlanarHom.PromisedFPReductionClosure

/-! NEW assembly of recovered Corollary 11.2 against the genuine reconstructed
main theorem. Its explicit hardness premise is the Potts foundation. The easy
branch and all-zero-weight algorithm use the already proved Ising foundation.
The exact zero-weight deletion and original-field source programs are retained. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ}

def SurvivingWeightedClass (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) : Prop :=
  PositiveVertexWeightClass (L.positiveLanguage.matrices 0) L.positiveLanguage.weights
    (fun i j=>hs (L.positiveIndex i).val (L.positiveIndex j).val)

theorem surviving_weighted_class_inFP (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hw : ∀i,0≤L.weights i)
    (h : L.SurvivingWeightedClass hs) : L.problem.InFP :=
  (L.removeNonpositiveColorsReduction hw).inFP
    (L.positiveLanguage.positive_vertex_weight_class_inFP (fun i j=>hs _ _) h)

theorem corollary112_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0≤L.weights i) :
    (L.SurvivingWeightedClass hs → L.problem.InFP) ∧
    (¬L.SurvivingWeightedClass hs → PromisedSharpPHard L.problem) := by
  have hh:=L.positiveLanguage.theorem13_of_potts hPotts
    (fun i j=>hs (L.positiveIndex i).val (L.positiveIndex j).val)
    (fun i j=>hnn _ _) L.positiveLanguage_weights
  refine ⟨L.surviving_weighted_class_inFP hs hw,?_⟩
  intro hbad
  exact (hh.2 hbad).trans (L.restoreZeroColorsReduction hw)

theorem corollary112_dichotomy_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0≤L.weights i) :
    L.problem.InFP ∨ PromisedSharpPHard L.problem := by
  by_cases hc : L.SurvivingWeightedClass hs
  · exact Or.inl ((L.corollary112_of_potts hPotts hs hnn hw).1 hc)
  · exact Or.inr ((L.corollary112_of_potts hPotts hs hnn hw).2 hc)

theorem surviving_class_zero_weights (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hw : ∀i,L.weights i=0) :
    L.SurvivingWeightedClass hs := by
  letI : IsEmpty L.PositiveColors := ⟨fun i=>by have h:=i.property; rw [hw] at h; exact (lt_irrefl 0) h⟩
  have hc : Fintype.card L.PositiveColors=0 := Fintype.card_eq_zero
  letI : IsEmpty (Fin (Fintype.card L.PositiveColors)) :=
    Fintype.card_eq_zero_iff.mp (by simpa only [Fintype.card_fin] using hc)
  unfold SurvivingWeightedClass PositiveVertexWeightClass WeightedClass
  refine ⟨0,(fun i=>isEmptyElim i),?_,?_,?_⟩
  · intro r; exact r.elim0
  · intro i; exact isEmptyElim i
  · intro r; exact r.elim0

theorem zero_vertex_weights_inFP (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hw : ∀i,L.weights i=0) :
    L.problem.InFP :=
  L.surviving_weighted_class_inFP hs (fun i=>le_of_eq (hw i).symm)
    (L.surviving_class_zero_weights hs hw)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
