import PlanarHom.RectangularAllDegreeRigidity
import PlanarHom.RectangularSourceFourierBlocks

/-! NEW complete mixed Walsh classification of the literal original matrix.
The source equations yield degree preservation; physical-square coefficients
force a signed coordinate permutation in degree one and all higher degrees.
The final coordinate map is a genuine Boolean color equivalence. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem character_weight_sum (θ:Fin d→ℝ) (x y:Cube d):
    (∑S:Cube d,characterWeight θ S*character S x*character S y)=
      ∏i:Fin d,(1+θ i*bitCharacter true (x i)*bitCharacter true (y i)):=by
  simp only [characterWeight_product,character,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (s:Bool)=>(if s then θ i else 1)*bitCharacter s (x i)*bitCharacter s (y i))]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> simp [bitCharacter] <;> ring

theorem physical_permutation_entries (C:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (p:Fin d≃Fin d) (flip:Fin d→Bool)
    (hC:∀S T,C S T=characterWeight θ S*permutationRow p flip S T) (x y:Cube d):
    physicalValues C x y=
      ∏i:Fin d,(1+θ i*bitCharacter true (x i)*bitCharacter true (signedColorEquiv p flip y i)):=by
  rw [physicalValues_apply,←character_weight_sum]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [hC]
  simp only [permutationRow,mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [signedColor_character]
  ring

theorem bit_factor_to_tensor (θ:ℝ) (hθ:0<θ) (x y:Bool):
    1+θ*bitCharacter true x*bitCharacter true y=(1+θ)*Boolean.W ((1-θ)/(1+θ)) x y:=by
  have hn:1+θ≠0:=ne_of_gt (by linarith)
  cases x <;> cases y <;> simp [bitCharacter,Boolean.W] <;> field_simp [hn] <;> ring

theorem reconstruct_original_tensor (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ) (hs0:0<s0)
    (θ:Fin d→ℝ) (hθ:∀i,0<θ i ∧ θ i<1) (p:Fin d≃Fin d) (flip:Fin d→Bool)
    (hC:∀S T,normalizedCoefficients B s0 S T=characterWeight θ S*permutationRow p flip S T):
    ∃f:Cube d≃Cube d,∃c:ℝ,∃ρ:Fin d→ℝ,0<c ∧ (∀i,0<ρ i ∧ ρ i<1) ∧
      ∀x y,B x y=c*Boolean.tensor ρ x (f y):=by
  let ρ:Fin d→ℝ:=fun i=>(1-θ i)/(1+θ i)
  let c:ℝ:=(s0/(2:ℝ)^d)*(∏ i : Fin d, (1+θ i))
  have hc:0<c:=mul_pos (div_pos hs0 (pow_pos (by norm_num) _))
    (Finset.prod_pos (fun i _=>by linarith [(hθ i).1]))
  have hρ:∀i,0<ρ i ∧ ρ i<1:=by
    intro i
    have hden:0<1+θ i:=by linarith [(hθ i).1]
    exact ⟨div_pos (sub_pos.mpr (hθ i).2) hden,(div_lt_one hden).mpr (by linarith [(hθ i).1])⟩
  refine ⟨signedColorEquiv p flip,c,ρ,hc,hρ,?_⟩
  have hback:(s0/(2:ℝ)^d) • physicalValues (normalizedCoefficients B s0)=B:=by
    rw [normalizedCoefficients,physicalValues_smul,source_inversion,smul_smul]
    have he:(s0/(2:ℝ)^d)*((2:ℝ)^d/s0)=1:=by field_simp
    rw [he,one_smul]
  intro x y
  have he:=congrFun (congrFun hback x) y
  rw [Matrix.smul_apply,smul_eq_mul,physical_permutation_entries _ θ p flip hC] at he
  rw [←he]
  simp_rw [bit_factor_to_tensor _ (hθ _).1]
  rw [Finset.prod_mul_distrib]
  change (s0/(2:ℝ)^d)*((∏ i : Fin d, (1+θ i))*Boolean.tensor ρ x (signedColorEquiv p flip y))=
    ((s0/(2:ℝ)^d)*(∏ i : Fin d, (1+θ i)))*Boolean.tensor ρ x (signedColorEquiv p flip y)
  ring

/-- Exact interface required by the recovered physical rectangular consumer.
Only its actual Gram/noise/parallel-square equations are hypotheses. -/
theorem original_tensor_form_of_mixed_gram
    (B:Matrix (Cube d) (Cube d) ℝ) (hB:∀x y,0<B x y) (γX γY:ℝ)
    (ρX ρY:Fin d→ℝ) (hρX:∀i,0<ρX i ∧ ρX i<1)
    (hX:∀x y,(B*B.transpose) x y=γX*Boolean.tensor ρX x y)
    (hY:∀x y,(B.transpose*B) x y=γY*Boolean.tensor ρY x y)
    (z:ℝ) (hz:0<z) (hz1:z<1) (γ:ℝ) (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0)
    (hmix:B*noiseMatrix z*B.transpose=γ • Boolean.tensor ρ)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃σ:Fin d→ℝ,(∀i,0<σ i) ∧
      physicalGram (sourceCoefficients B) (t:ℝ)=δ • Boolean.tensor σ):
    ∃f:Cube d≃Cube d,∃c:ℝ,∃σ:Fin d→ℝ,0<c ∧ (∀i,0<σ i ∧ σ i<1) ∧
      ∀x y,B x y=c*Boolean.tensor σ x (f y):=by
  obtain ⟨s0,hs0,θ,hθ,O,hO,hrep,hdeg,h00,_,hrow⟩:=
    source_degree_blocks B hB γX γY ρX ρY hρX hX hY z γ hz hz1 ρ hρ hmix
  let C:=normalizedCoefficients B s0
  have hformsC:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃σ:Fin d→ℝ,(∀i,0<σ i) ∧
      physicalGram C (t:ℝ)=δ • Boolean.tensor σ:=by
    intro t ht ht1
    obtain ⟨δ,σ,hσ,he⟩:=hforms t ht ht1
    refine ⟨((2:ℝ)^d/s0)^4*δ,σ,hσ,?_⟩
    change physicalGram (normalizedCoefficients B s0) (t:ℝ)=_
    rw [normalizedCoefficients,physicalGram_smul,he,smul_smul]
  have hnorm:=block_leading_norms C O θ hO hrep hrow hformsC
  obtain ⟨p,flip,hall⟩:=all_degree_permutation C O θ (fun i=>(hθ i).1) hO hrep hdeg h00 hrow hnorm
  apply reconstruct_original_tensor B s0 hs0 θ hθ p flip
  intro S T
  rw [hrep,hall]

end PlanarHom.RectangularWalshConvolution
