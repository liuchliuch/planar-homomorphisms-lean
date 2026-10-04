import PlanarHom.RectangularSourceOrthogonalData
import PlanarHom.RectangularPhysicalGramDefinitions

/-! NEW actual source-to-degree-block assembly and literal normalization of the
parallel-square Gram. No Fourier block or coefficient identity is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem source_degree_blocks (B:Matrix (Cube d) (Cube d) ℝ) (hB:∀i j,0<B i j)
    (γX γY:ℝ) (ρX ρY:Fin d→ℝ) (hρX:∀i,0<ρX i ∧ ρX i<1)
    (hX:∀i j,(B*B.transpose) i j=γX*Boolean.tensor ρX i j)
    (hY:∀i j,(B.transpose*B) i j=γY*Boolean.tensor ρY i j)
    (z γ:ℝ) (hz:0<z) (hz1:z<1) (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0)
    (hmix:B*noiseMatrix z*B.transpose=γ • Boolean.tensor ρ):
    ∃s0:ℝ,0<s0 ∧ ∃θ:Fin d→ℝ,(∀i,0<θ i ∧ θ i<1) ∧
      ∃O:Matrix (Cube d) (Cube d) ℝ,O*O.transpose=1 ∧
        (∀S T,normalizedCoefficients B s0 S T=characterWeight θ S*O S T) ∧
        (∀S T,Boolean.degree S≠Boolean.degree T→O S T=0) ∧
        O (fun _=>false) (fun _=>false)=1 ∧
        (∀S,S≠(fun _=>false)→O S (fun _=>false)=0) ∧
        (∀T,normalizedCoefficients B s0 (fun _=>false) T=if T=(fun _=>false) then 1 else 0):=by
  obtain ⟨s0,hs0,_,_,hrow,hcol⟩:=exists_normalized_constant_mode B hB γX γY ρX ρY hX hY
  have hX':B*B.transpose=γX • Boolean.tensor ρX:=by funext i j;exact hX i j
  obtain ⟨θ,hθ,O,hO,hrep,hdeg,h00,hOcol⟩:=orthogonal_data_of_tensor_grams
    (normalizedCoefficients B s0) hrow hcol (γX/s0^2) ρX hρX
    (normalized_gram B s0 hs0.ne' γX ρX hX') z (γ/s0^2) hz hz1 ρ hρ
    (normalized_mixedGram B s0 hs0.ne' z γ ρ hmix)
  exact ⟨s0,hs0,θ,hθ,O,hO,hrep,hdeg,h00,hOcol,hrow⟩

theorem noiseValues_smul (c:ℝ) (C:Matrix (Cube d) (Cube d) ℝ) (t:ℝ):
    noiseValues (c • C) t=c • noiseValues C t:=by
  simp only [noiseValues,Matrix.mul_smul,Matrix.smul_mul]

theorem squaredNoise_smul (c:ℝ) (C:Matrix (Cube d) (Cube d) ℝ) (t:ℝ):
    squaredNoise (c • C) t=c^2 • squaredNoise C t:=by
  funext x y
  simp only [squaredNoise,noiseValues_smul,Matrix.smul_apply,smul_eq_mul]
  ring

theorem physicalGram_smul (c:ℝ) (C:Matrix (Cube d) (Cube d) ℝ) (t:ℝ):
    physicalGram (c • C) t=c^4 • physicalGram C t:=by
  simp only [physicalGram,squaredNoise_smul,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  ring

theorem normalized_physical_forms (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      parallelSquareGram B (t:ℝ)=δ • Boolean.tensor ρ):
    ∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      physicalGram (normalizedCoefficients B s0) (t:ℝ)=δ • Boolean.tensor ρ:=by
  intro t ht ht1
  obtain ⟨δ,ρ,hρ,hform⟩:=hforms t ht ht1
  refine ⟨((2:ℝ)^d/s0)^4*(((2:ℝ)^d)⁻¹^2*δ),ρ,hρ,?_⟩
  rw [normalizedCoefficients,physicalGram_smul,physicalGram_source,hform,smul_smul,smul_smul]
  simp only [mul_assoc]

end PlanarHom.RectangularWalshConvolution
