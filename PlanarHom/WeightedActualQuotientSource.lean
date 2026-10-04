import PlanarHom.FiniteFieldQuotientLanguage
import PlanarHom.WeightedStructureTransport
import PlanarHom.ActualTwinRealAvailability
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ}
def fullQuotientLanguage (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :=
  FiniteFieldQuotientLanguage.language L.basis (L.matricesK 0) (L.actualTwin_symmetryK hs) L.weightsK
def fullQuotientSourceReduction (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    PromisePolyTimeTuringReduction (L.fullQuotientLanguage hs).problem L.problem :=
  (FiniteFieldQuotientLanguage.reduction L.basis (L.matricesK 0) (L.actualTwin_symmetryK hs) L.weightsK).trans
    (L.corollary38_quotient hs)
theorem fullQuotient_injective_rows (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    Function.Injective ((L.fullQuotientLanguage hs).matrices 0) :=
  FiniteFieldQuotientLanguage.real_matrix_rows_injective (L.matricesK 0) (L.actualTwin_symmetryK hs)
theorem fullQuotient_weights_positive (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) (hw : ∀ i,0<L.weights i) :
    ∀ i,0<(L.fullQuotientLanguage hs).weights i := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  exact fun i=>Twins.quotientWeight_pos (L.matricesK 0) L.weightsK hw _
theorem fullQuotient_weighted_class_iff (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    WeightedClass ((L.fullQuotientLanguage hs).matrices 0) (L.fullQuotientLanguage hs).weights ↔
      PositiveVertexWeightClass (L.matrices 0) L.weights hs := by
  let er := FiniteFieldQuotientLanguage.realQuotientEquiv (L.matricesK 0) (L.matrices 0) (fun _ _=>rfl)
  let e := (FiniteFieldQuotientLanguage.index (L.matricesK 0)).trans er
  have hm : (L.fullQuotientLanguage hs).matrices 0=
      (fun i j=>Twins.quotientMatrix (L.matrices 0) hs (e i) (e j)) := by
    funext i j
    exact FiniteFieldQuotientLanguage.quotientMatrix_real (L.matricesK 0)
      (L.actualTwin_symmetryK hs) (L.matrices 0) hs (fun _ _=>rfl) _ _
  have hw : (L.fullQuotientLanguage hs).weights=
      (fun i=>Twins.quotientWeight (L.matrices 0) L.weights (e i)) := by
    funext i
    exact FiniteFieldQuotientLanguage.quotientWeight_real (L.matricesK 0) (L.matrices 0)
      (fun _ _=>rfl) L.weightsK _
  rw [hm,hw]
  exact ⟨fun h=>WeightedClass.of_equiv e h,fun h=>h.equiv e⟩
end PlanarHom.AlgebraicProductInterpolation.RealLanguage
