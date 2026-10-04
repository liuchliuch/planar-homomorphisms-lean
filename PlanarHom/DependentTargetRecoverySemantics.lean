import PlanarHom.DependentTargetAggregation
import PlanarHom.CrossFieldInterpolationSemantics

/-! The clipped total recovery machine agrees with exact cross-field interpolation on honest rows. -/
noncomputable section
namespace PlanarHom.DependentTargetAggregation
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (inclusion : ∀ x, L →+* K x) {t : ℕ} (B : ∀ x, Fin t → K x)

theorem recover_eq (x : X) (m : ℕ) (rows : List (L × List ℕ)) (answers : List L)
    (hrows : ∀ row ∈ rows, row.2 ∈ ExponentVectors.weak t m) :
    recover K inclusion B ((x,m),(rows,answers)) =
      ⟨x,CrossFieldInterpolationSemantics.aggregate (inclusion x) (B x) rows answers⟩ := by
  apply aggregate_eq
  intro row hr
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hr
  exact hrows original ho

theorem recover_representatives (x : X) (m : ℕ) (A : Fin t → L) (answers : List L) :
    recover K inclusion B ((x,m),(SourceExponentRepresentatives.representatives A m,answers)) =
      ⟨x,CrossFieldInterpolationSemantics.aggregate (inclusion x) (B x)
        (SourceExponentRepresentatives.representatives A m) answers⟩ :=
  recover_eq K inclusion B x m _ answers (fun row hr =>
    (SourceExponentRepresentatives.mem_representatives A m row hr).1)

end PlanarHom.DependentTargetAggregation
