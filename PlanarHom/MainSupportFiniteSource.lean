import PlanarHom.RootedRealComponentAvailability
import PlanarHom.ActualTwinReduction
import PlanarHom.AlgebraicLanguagePresentation

/-! Exact recovered support-submatrix source programs, extracted without the
unrelated Gram-construction declarations. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q : ℕ}

def supportFiniteLanguage (L : RealLanguage q 1 0) (X : Set (Fin q)) [Fintype X] :
    RealLanguage (Fintype.card X) 1 0 where
  matrices := fun _ i j=>L.matrices 0 ((Fintype.equivFin X).symm i) ((Fintype.equivFin X).symm j)
  unaries := Fin.elim0
  weights := fun i=>L.weights ((Fintype.equivFin X).symm i)
  matrices_algebraic := fun _ _ _=>L.matrices_algebraic 0 _ _
  unaries_algebraic := fun u=>u.elim0
  weights_algebraic := fun _=>L.weights_algebraic _

def supportFiniteReduction (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) (hw : ∀ i,0<L.weights i)
    (X : Set (Fin q)) [fX : Fintype X] (hX : RootedRestriction.ColorClosed (L.matrices 0) X) :
    PromisePolyTimeTuringReduction (L.supportFiniteLanguage X).problem L.problem := by
  let fcanon : Fintype X := @Subtype.fintype (Fin q) (fun i=>i∈X)
    (fun i=>Classical.propDecidable (i∈X)) (Fin.fintype q)
  have hi : fX=fcanon := Subsingleton.elim _ _
  subst fX
  let e := (Fintype.equivFin X).symm
  have r₁ := (L.supportFiniteLanguage X).presentationDescentReduction L.field L.basis
    (fun _ : Fin 1=>fun i j=>L.matricesK 0 (e i) (e j)) (fun u : Fin 0=>u.elim0)
    (fun i=>L.weightsK (e i)) (fun _ _ _=>rfl) (fun u=>u.elim0) (fun _=>rfl)
  have r₂ := ActualTwins.reindexReduction L.basis
    (fun i j : X=>L.matricesK 0 i.val j.val) (fun i : X=>L.weightsK i.val) e
  exact r₁.trans (r₂.trans (L.lemma35_submatrix hs hw X hX))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
