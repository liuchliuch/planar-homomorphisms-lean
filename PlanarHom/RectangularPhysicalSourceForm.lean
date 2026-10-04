-- RECOVERED original classifier body. Mechanical shared-definition extraction:
-- parallelSquare, parallelSquareGram and physicalGram_source are imported
-- from RectangularPhysicalGramDefinitions to avoid duplicate declarations.
import PlanarHom.RectangularOriginalMixedTensorForm
import PlanarHom.RectangularGramRoots
import PlanarHom.RectangularPhysicalGramDefinitions
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open RectangularGramRoots
theorem rectangular_tensor_of_physical_forms {a b : ℕ}
    (B : Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (hB : ∀ x y,0<B x y)
    (h k : ℕ) (hh : h≠0) (hk : k≠0) (γX γY : ℝ)
    (ρX : Fin a → ℝ) (ρY : Fin b → ℝ)
    (hρX : ∀ i,0<ρX i ∧ ρX i<1) (hρY : ∀ i,0<ρY i ∧ ρY i<1)
    (hX : ∀ x y,((B*B.transpose) x y)^h=γX*Boolean.tensor ρX x y)
    (hY : ∀ x y,((B.transpose*B) x y)^k=γY*Boolean.tensor ρY x y)
    (z : ℝ) (hz : 0<z) (hz1 : z<1) (γ : ℝ) (ρ : Fin a → ℝ)
    (hρ : ∀ i,1+ρ i≠0) (hmix : B*noiseMatrix z*B.transpose=γ • Boolean.tensor ρ)
    (hforms : ∀ t : ℚ,0<t → t<1 → ∃ γ : ℝ,∃ ρ : Fin a → ℝ,
      (∀ i,0<ρ i) ∧ parallelSquareGram B (t:ℝ)=γ • Boolean.tensor ρ) :
    a=b ∧ ∃ f : Boolean.Cube b ≃ Boolean.Cube a,∃ γ : ℝ,∃ ρ : Fin a → ℝ,
      0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧ ∀ x y,B x y=γ*Boolean.tensor ρ x (f y) := by
  have hd := cube_dimensions_of_tensor_powers B hB h k hh hk γX γY ρX ρY hρX hρY hX hY
  subst b
  refine ⟨rfl,?_⟩
  have hpY : ∀ x y,0<(B.transpose*B) x y := by
    simpa only [Matrix.transpose_transpose] using positive_left_gram B.transpose (fun x y => hB y x)
  apply original_tensor_form_of_mixed_gram B hB (γX^((h:ℝ)⁻¹)) (γY^((k:ℝ)⁻¹))
    (rootParameters ρX h) (rootParameters ρY k) (root_range ρX hρX h hh)
    (positive_tensor_root _ (positive_left_gram B hB) h hh γX ρX hρX hX)
    (positive_tensor_root _ hpY k hk γY ρY hρY hY) z hz hz1 γ ρ hρ hmix
  intro t ht ht1
  obtain ⟨δ,σ,hσ,hs⟩ := hforms t ht ht1
  refine ⟨((2:ℝ)^a)⁻¹^2*δ,σ,hσ,?_⟩
  rw [physicalGram_source,hs,smul_smul]
end PlanarHom.RectangularWalshConvolution
