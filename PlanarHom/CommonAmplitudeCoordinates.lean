import PlanarHom.FiniteMomentFiberEquivalence
import Mathlib.Tactic.Linarith

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CommonAmplitudeCoordinates
variable {X S : Type} [Fintype X] [Nonempty S]

/-- Equal even moments on every actual class produce one common positive
amplitude vector and an actual class-respecting product coordinate bijection. -/
theorem exists_common_amplitude_chart (classOf : X → S) (hsurj : Function.Surjective classOf)
    (amplitude : X → ℝ) (hamp : ∀ x,0<amplitude x)
    (hmom : ∀ s t : S,∀ m : ℕ,
      (∑ x : {x // classOf x=s},(amplitude x.val)^(2*m))=
        ∑ y : {y // classOf y=t},(amplitude y.val)^(2*m)) :
    ∃ k : ℕ,∃ a : Fin k → ℝ,∃ e : X ≃ S×Fin k,
      0<k ∧ (∀ i,0<a i) ∧ (∀ x,(e x).1=classOf x) ∧ (∀ x,amplitude x=a (e x).2) := by
  let s0 : S := Classical.arbitrary S
  have hnon : Nonempty {x // classOf x=s0} := by
    obtain ⟨x,hx⟩ := hsurj s0
    exact ⟨⟨x,hx⟩⟩
  have hf : ∀ s : S,∃ e : {x // classOf x=s} ≃ {x // classOf x=s0},
      ∀ x,amplitude (e x).val=amplitude x.val := by
    intro s
    obtain ⟨e,he⟩ := FiniteMomentFiberEquivalence.exists_value_preserving_equiv
      (fun x : {x // classOf x=s} => (amplitude x.val)^2)
      (fun x : {x // classOf x=s0} => (amplitude x.val)^2) (by
        intro m
        simpa only [← pow_mul] using hmom s s0 m)
    refine ⟨e,?_⟩
    intro x
    have h := he x
    have ha := hamp (e x).val
    have hb := hamp x.val
    nlinarith
  choose E hE using hf
  let k := Fintype.card {x // classOf x=s0}
  let baseEnum : {x // classOf x=s0} ≃ Fin k := Fintype.equivFin _
  let a : Fin k → ℝ := fun i => amplitude (baseEnum.symm i).val
  let e : X ≃ S×Fin k := (Equiv.sigmaFiberEquiv classOf).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fun s => (E s).trans baseEnum))
  refine ⟨k,a,e,Fintype.card_pos_iff.mpr hnon,(fun i => hamp _),(fun x => rfl),?_⟩
  intro x
  change amplitude x=amplitude (baseEnum.symm (baseEnum (E (classOf x) ⟨x,rfl⟩))).val
  rw [baseEnum.symm_apply_apply]
  exact (hE (classOf x) ⟨x,rfl⟩).symm

end PlanarHom.CommonAmplitudeCoordinates
