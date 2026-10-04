import PlanarHom.RectangularNoiseZeroCoefficient

/-! NEW exact first-degree coefficient of the physical parallel square. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {d:ℕ}

theorem singleton_ne_zero (i:Fin d):unitBit i≠(fun _=>false):=by
  intro h
  have hi:=congrFun h i
  simp [unitBit] at hi

theorem minimal_singleton_split (i:Fin d) (I:Cube d):
    Boolean.degree I+Boolean.degree (xor (unitBit i) I)=1↔I=(fun _=>false) ∨ I=unitBit i:=by
  have hd:Boolean.degree (unitBit i)=1:=by rw [degree_eq_support_card,support_unitBit,Finset.card_singleton]
  rw [←hd,minimal_split_iff,support_unitBit,Finset.subset_singleton_iff]
  constructor
  · rintro (h|h)
    · left
      apply (bitSetEquiv d).injective
      change bitSupport I=bitSupport (fun _=>false)
      simpa [bitSupport] using h
    · right
      apply (bitSetEquiv d).injective
      change bitSupport I=bitSupport (unitBit i)
      simpa only [support_unitBit] using h
  · rintro (rfl|rfl)
    · left;simp [bitSupport]
    · right;exact support_unitBit i

theorem squareCoefficient_singleton (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (i:Fin d) (T:Cube d):
    (squareCoefficientPolynomial C (unitBit i) T).coeff 1=2*C (unitBit i) T:=by
  rw [squarePolynomial_coeff]
  simp only [Fintype.sum_prod_type,minimal_singleton_split]
  have hsplit (I J:Cube d):
      (if I=(fun _=>false) ∨ I=unitBit i then C I J*C (xor (unitBit i) I) (xor T J) else 0)=
      (if I=(fun _=>false) then C I J*C (xor (unitBit i) I) (xor T J) else 0)+
      (if I=unitBit i then C I J*C (xor (unitBit i) I) (xor T J) else 0):=by
    by_cases h0:I=(fun _=>false)
    · subst I
      simp [singleton_ne_zero i|>.symm]
    · by_cases hi:I=unitBit i <;> simp [h0,hi,singleton_ne_zero i]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,xor_zero_right,xor_self_zero,hrow]
  simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,xor_eq_zero_iff]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true,xor_zero_right]
  ring

theorem singleton_rowNorm_coeff (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0) (i:Fin d):
    (rowNormPolynomial C (unitBit i)).coeff 2=4*(∑T:Cube d,C (unitBit i) T^2):=by
  have hd:Boolean.degree (unitBit i)=1:=by rw [degree_eq_support_card,support_unitBit,Finset.card_singleton]
  have h:=rowNormPolynomial_first_coeff C (unitBit i)
  rw [hd,Nat.mul_one] at h
  rw [h]
  simp_rw [squareCoefficient_singleton C hrow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem square_leading_norm_identity (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      physicalGram C (t:ℝ)=δ • Boolean.tensor ρ) (S:Cube d):
    (∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(∏i∈bitSupport S,∑T:Cube d,C (unitBit i) T^2):=by
  rw [←rowNormPolynomial_first_coeff,rowNorm_first_tensor_product C hrow hforms]
  simp_rw [singleton_rowNorm_coeff C hrow]
  rw [Finset.prod_mul_distrib,Finset.prod_const,←degree_eq_support_card]

end PlanarHom.RectangularWalshConvolution
