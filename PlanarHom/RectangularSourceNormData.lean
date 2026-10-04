import PlanarHom.RectangularSourceFourierBlocks
import PlanarHom.RectangularSingletonCoefficient

/-! NEW source-derived norm equalities for every Fourier degree. This closes
the actual gadget-to-coefficient boundary used by the final rigidity induction. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem orthogonal_row_norm (O:Matrix (Cube d) (Cube d) ℝ) (hO:O*O.transpose=1) (S:Cube d):
    (∑T:Cube d,O S T^2)=1:=by
  have h:=congrFun (congrFun hO S) S
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two] using h

@[simp] theorem characterWeight_singleton (θ:Fin d→ℝ) (i:Fin d):characterWeight θ (unitBit i)=θ i:=by
  rw [characterWeight,support_unitBit,Finset.prod_singleton]

theorem block_leading_norms (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hO:O*O.transpose=1) (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧ physicalGram C (t:ℝ)=δ • Boolean.tensor ρ):
    ∀S,(∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(characterWeight θ S)^2:=by
  intro S
  rw [square_leading_norm_identity C hrow hforms]
  have hsingle:∀i,(∑T:Cube d,C (unitBit i) T^2)=(θ i)^2:=by
    intro i
    simp_rw [hrep,characterWeight_singleton,mul_pow]
    rw [←Finset.mul_sum,orthogonal_row_norm O hO,mul_one]
  simp_rw [hsingle]
  rw [Finset.prod_pow]
  rfl

theorem source_norm_data (B:Matrix (Cube d) (Cube d) ℝ) (hB:∀i j,0<B i j)
    (γX γY:ℝ) (ρX ρY:Fin d→ℝ) (hρX:∀i,0<ρX i ∧ ρX i<1)
    (hX:∀i j,(B*B.transpose) i j=γX*Boolean.tensor ρX i j)
    (hY:∀i j,(B.transpose*B) i j=γY*Boolean.tensor ρY i j)
    (z γ:ℝ) (hz:0<z) (hz1:z<1) (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0)
    (hmix:B*noiseMatrix z*B.transpose=γ • Boolean.tensor ρ)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃σ:Fin d→ℝ,(∀i,0<σ i) ∧
      parallelSquareGram B (t:ℝ)=δ • Boolean.tensor σ):
    ∃s0:ℝ,0<s0 ∧ ∃θ:Fin d→ℝ,(∀i,0<θ i ∧ θ i<1) ∧
      ∃O:Matrix (Cube d) (Cube d) ℝ,O*O.transpose=1 ∧
        (∀S T,normalizedCoefficients B s0 S T=characterWeight θ S*O S T) ∧
        (∀S T,Boolean.degree S≠Boolean.degree T→O S T=0) ∧
        O (fun _=>false) (fun _=>false)=1 ∧
        (∀S,S≠(fun _=>false)→O S (fun _=>false)=0) ∧
        (∀S,(∑T:Cube d,((squareCoefficientPolynomial (normalizedCoefficients B s0) S T).coeff
          (Boolean.degree S))^2)=4^(Boolean.degree S)*(characterWeight θ S)^2):=by
  obtain ⟨s0,hs0,θ,hθ,O,hO,hrep,hdeg,h00,hOcol,hrow⟩:=source_degree_blocks B hB γX γY ρX ρY hρX
    hX hY z γ hz hz1 ρ hρ hmix
  exact ⟨s0,hs0,θ,hθ,O,hO,hrep,hdeg,h00,hOcol,
    block_leading_norms _ O θ hO hrep hrow (normalized_physical_forms B s0 hforms)⟩

end PlanarHom.RectangularWalshConvolution
