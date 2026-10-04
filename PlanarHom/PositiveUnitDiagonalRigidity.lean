import PlanarHom.PositiveSymmetricTensorDamping
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveUnitDiagonalRigidity
open PositiveSymmetricTensorDamping
theorem proportional_rows_equal {I : Type} (B : Matrix I I ℝ)
    (hs : ∀ i j,B i j=B j i) (hpos : ∀ i j,0<B i j) (hdiag : ∀ i,B i i=1)
    (i j : I) (r : ℝ) (h : ∀ k,B i k=r*B j k) : r=1 ∧ B i=B j := by
  have hi := h i
  have hj := h j
  rw [hdiag i,hs j i] at hi
  rw [hdiag j,mul_one] at hj
  have hr : 0<r := hj ▸ hpos i j
  have he : r=1 := by rw [hj] at hi; nlinarith
  exact ⟨he,funext (fun k => by simpa only [he,one_mul] using h k)⟩
theorem tensor_unit_parameter_equal_rows {d : ℕ} (ρ : Fin d → ℝ) (i : Fin d) (hi : ρ i=1) :
    Boolean.tensor ρ (Boolean.unitBit i)=Boolean.tensor ρ (fun _ => false) := by
  funext y
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : j=i
  · subst j
    cases y i <;> simp [Boolean.unitBit,Boolean.W,hi]
  · simp [Boolean.unitBit,hij]
theorem tensor_parameters_nonunit {d : ℕ} (ρ : Fin d → ℝ)
    (hinj : Function.Injective (Boolean.tensor ρ)) : ∀ i,ρ i≠1 := by
  intro i hi
  have he := hinj (tensor_unit_parameter_equal_rows ρ i hi)
  have hf := congrFun he i
  simpa [Boolean.unitBit] using hf
theorem unit_diagonal_tensor_core {d : ℕ} (B : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (hB : B.IsHermitian) (hpos : ∀ x y,0<B x y) (hdiag : ∀ x,B x x=1)
    (hinj : Function.Injective B)
    (hclass : ∀ t : ℚ,0<t → t<1 → (damped B (t:ℝ)).PosDef →
      ∃ γ : ℝ,∃ ρ : Fin d → ℝ,0<γ ∧ (∀ i,0<ρ i) ∧ damped B (t:ℝ)=γ • Boolean.tensor ρ) :
    ∃ ρ : Fin d → ℝ,(∀ i,0<ρ i ∧ ρ i≠1) ∧ B=Boolean.tensor ρ ∧ IsUnit B := by
  obtain ⟨γ,ρ,hγ,hρ,hform⟩ := tensor_of_positive_definite_dampings B hB hpos hclass
  have hg : γ=1 := by
    have hv := congrArg (fun M : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ => M (fun _ => false) (fun _ => false)) hform
    change B (fun _ => false) (fun _ => false)=γ*Boolean.tensor ρ (fun _ => false) (fun _ => false) at hv
    simpa only [hdiag,Boolean.tensor_diag,mul_one] using hv.symm
  have he : B=Boolean.tensor ρ := by simpa only [hg,one_smul] using hform
  have hn := tensor_parameters_nonunit ρ (he ▸ hinj)
  refine ⟨ρ,(fun i => ⟨hρ i,hn i⟩),he,?_⟩
  rw [he]
  exact (Boolean.tensor_isUnit_iff_of_pos hρ).mpr hn
end PlanarHom.PositiveUnitDiagonalRigidity
