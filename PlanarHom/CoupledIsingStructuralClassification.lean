import PlanarHom.CoupledIsingTensorChart
import PlanarHom.BinaryCharacterStructuralObstruction

noncomputable section
open Classical
namespace PlanarHom.CoupledIsing
open BinaryCharacters Structures
variable {n m:ℕ}

theorem map_surjective_of_image_card (a:Fin m→Space n)
    (hc:Fintype.card (ImageSpace a)=2^m) : Function.Surjective (characterMap a) := by
  have he:Fintype.card (ImageSpace a)=Fintype.card (Space m) := by
    simpa [Space,Fintype.card_fun,ZMod.card] using hc
  have hs:Function.Surjective (Subtype.val:ImageSpace a→Space m):=
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective,he⟩).2
  intro z
  obtain ⟨x,hx⟩:=hs z
  obtain ⟨v,hv⟩:=x.property
  exact ⟨v,hv.trans hx⟩

theorem weighted_class_iff (a:Fin m→Space n) (ha:Function.Injective a)
    (hn:∀r,a r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0)
    (w:Space n→ℝ) (hw:∀x,0 < w x) :
    PositiveVertexWeightClass (interaction a J) w (symmetric a J) ↔
      LinearIndependent F₂ a ∧ ∃μ:ℝ,0 < μ ∧ ∀z,aggregatedWeight a w z=μ := by
  rw [weighted_class_iff_quotient a ha J hJ w]
  constructor
  · intro h
    have hsep:∀x y:ImageSpace a,(∀r,coordinate a r x=coordinate a r y)→x=y := by
      intro x y hxy
      apply Subtype.ext
      funext r
      exact hxy r
    obtain ⟨hc,μ,hμ,hconst⟩:=BinaryCharacters.structural_cardinality_and_weight
      (coordinate a) (coordinate_injective a ha) (coordinate_ne_zero a hn) hsep
      J hJ (aggregatedWeight a w) (aggregatedWeight_positive a w hw) h
    exact ⟨(map_surjective_iff_independent a).mp (map_surjective_of_image_card a hc),μ,hμ,hconst⟩
  · rintro ⟨hi,μ,hμ,hconst⟩
    exact quotient_weightedClass_of_independent a hi J hJ _ μ hμ hconst

end PlanarHom.CoupledIsing
