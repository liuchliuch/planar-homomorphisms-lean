import PlanarHom.ZeroWeightSourceReduction
import PlanarHom.AlgebraicLanguagePresentation
import PlanarHom.MixedColorEquivalence

noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q bt ut : ℕ}

abbrev PositiveColors (L : RealLanguage q bt ut) := {i : Fin q // 0<L.weights i}

def positiveIndex (L : RealLanguage q bt ut) : Fin (Fintype.card L.PositiveColors)≃L.PositiveColors :=
  (Fintype.equivFin _).symm

def positiveLanguage (L : RealLanguage q bt ut) : RealLanguage (Fintype.card L.PositiveColors) bt ut where
  matrices := fun l i j=>L.matrices l (L.positiveIndex i).val (L.positiveIndex j).val
  unaries := fun l i=>L.unaries l (L.positiveIndex i).val
  weights := fun i=>L.weights (L.positiveIndex i).val
  matrices_algebraic := fun l i j=>L.matrices_algebraic l (L.positiveIndex i).val (L.positiveIndex j).val
  unaries_algebraic := fun l i=>L.unaries_algebraic l (L.positiveIndex i).val
  weights_algebraic := fun i=>L.weights_algebraic (L.positiveIndex i).val

def positiveMatricesK (L : RealLanguage q bt ut) :=
  fun (l : Fin bt) (i j : Fin (Fintype.card L.PositiveColors))=>
    L.matricesK l (L.positiveIndex i).val (L.positiveIndex j).val

def positiveUnariesK (L : RealLanguage q bt ut) :=
  fun (l : Fin ut) (i : Fin (Fintype.card L.PositiveColors))=>L.unariesK l (L.positiveIndex i).val

def positiveWeightsK (L : RealLanguage q bt ut) :=
  fun (i : Fin (Fintype.card L.PositiveColors))=>L.weightsK (L.positiveIndex i).val

theorem positiveLanguage_weights (L : RealLanguage q bt ut) :
    ∀ i,0<L.positiveLanguage.weights i := fun i=>(L.positiveIndex i).property

theorem evaluate_positiveLanguage (L : RealLanguage q bt ut) (hw : ∀ i,0≤L.weights i)
    (g : MixedCode) (hg : g.Valid bt ut) :
    g.evaluate hg L.positiveMatricesK L.positiveUnariesK L.positiveWeightsK=
      g.evaluate hg L.matricesK L.unariesK L.weightsK := by
  have hz : ∀ i,¬0<L.weights i→L.weightsK i=0 := by
    intro i hi
    apply Subtype.ext
    exact le_antisymm (le_of_not_gt hi) (hw i)
  have h := evaluate_restrict_zero_weights g hg L.matricesK L.unariesK L.weightsK
    (fun i=>0<L.weights i) hz
  have he := evaluate_color_equiv L.positiveIndex g hg
    (fun l (i j : L.PositiveColors)=>L.matricesK l i.val j.val)
    (fun l (i : L.PositiveColors)=>L.unariesK l i.val) (fun (i : L.PositiveColors)=>L.weightsK i.val)
  exact he.trans h.symm

def removeNonpositiveColorsReduction (L : RealLanguage q bt ut) (hw : ∀ i,0≤L.weights i) :
    PromisePolyTimeTuringReduction L.problem L.positiveLanguage.problem :=
  (sameGraphColorReduction L.basis L.matricesK L.unariesK L.weightsK
    L.positiveMatricesK L.positiveUnariesK L.positiveWeightsK
    (fun g hg=>L.evaluate_positiveLanguage hw g hg)).trans
  (L.positiveLanguage.presentationMapReduction L.field L.basis
    L.positiveMatricesK L.positiveUnariesK L.positiveWeightsK
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl))

def restoreZeroColorsReduction (L : RealLanguage q bt ut) (hw : ∀ i,0≤L.weights i) :
    PromisePolyTimeTuringReduction L.positiveLanguage.problem L.problem :=
  (L.positiveLanguage.presentationDescentReduction L.field L.basis
    L.positiveMatricesK L.positiveUnariesK L.positiveWeightsK
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl)).trans
  (sameGraphColorReduction L.basis L.positiveMatricesK L.positiveUnariesK L.positiveWeightsK
    L.matricesK L.unariesK L.weightsK (fun g hg=>(L.evaluate_positiveLanguage hw g hg).symm))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
