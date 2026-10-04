import PlanarHom.RectangularNormalizedGram
import PlanarHom.RectangularTensorDegreeForcing
import PlanarHom.RectangularTensorNormPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! NEW actual orthogonal degree-block data derived from two displayed Fourier
Gram tensor equations. Distinct coordinate eigenvalues are not assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

def characterWeight (θ:Fin d→ℝ) (S:Cube d):ℝ:=∏i∈bitSupport S,θ i

theorem orthogonal_data_of_tensor_grams (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hcol:∀S,C S (fun _=>false)=if S=(fun _=>false) then 1 else 0)
    (δX:ℝ) (ρX:Fin d→ℝ) (hρX:∀i,0<ρX i ∧ ρX i<1)
    (hX:C*C.transpose=δX • Matrix.diagonal (eigenvalue ρX))
    (z δ:ℝ) (hz:0<z) (hz1:z<1) (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0)
    (hZ:C*noiseDiagonal z*C.transpose=δ • Matrix.diagonal (eigenvalue ρ)):
    ∃θ:Fin d→ℝ,(∀i,0<θ i ∧ θ i<1) ∧
    ∃O:Matrix (Cube d) (Cube d) ℝ,O*O.transpose=1 ∧
      (∀S T,C S T=characterWeight θ S*O S T) ∧
      (∀S T,Boolean.degree S≠Boolean.degree T→O S T=0) ∧
      O (fun _=>false) (fun _=>false)=1 ∧
      (∀S,S≠(fun _=>false)→O S (fun _=>false)=0):=by
  let zero:Cube d:=fun _=>false
  let w:Cube d→ℝ:=fun S=>δX*eigenvalue ρX S
  have hw0:w zero=1:=by
    have h:=congrFun (congrFun hX zero) zero
    simpa [zero,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,hrow] using h.symm
  have hrat:∀i,0<eigenRatio ρX i ∧ eigenRatio ρX i<1:=by
    intro i
    have hi:=hρX i
    constructor
    · exact div_pos (sub_pos.mpr hi.2) (by linarith)
    · apply (div_lt_one (by linarith : 0<1+ρX i)).mpr
      linarith
  have hXden:∀i,1+ρX i≠0:=fun i=>ne_of_gt (by linarith [(hρX i).1])
  have hwprod:∀S,w S=∏i∈bitSupport S,eigenRatio ρX i:=by
    intro S
    have he:=eigenvalue_support_product ρX hXden S
    change δX*eigenvalue ρX S=_
    rw [he,←mul_assoc,show δX*eigenvalue ρX zero=1 from hw0,one_mul]
  let θ:Fin d→ℝ:=fun i=>Real.sqrt (eigenRatio ρX i)
  have hθ:∀i,0<θ i ∧ θ i<1:=by
    intro i
    exact ⟨Real.sqrt_pos.mpr (hrat i).1,by simpa using Real.sqrt_lt_sqrt (hrat i).1.le (hrat i).2⟩
  let Θ:=characterWeight θ
  have hΘ:∀S,0<Θ S:=fun S=>Finset.prod_pos (fun i _=>(hθ i).1)
  have hΘ0:Θ zero=1:=by simp [Θ,characterWeight,zero,bitSupport]
  have hw:∀S,w S=Θ S^2:=by
    intro S
    rw [hwprod]
    change _=(∏i∈bitSupport S,Real.sqrt (eigenRatio ρX i))^2
    rw [←Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    exact (Real.sq_sqrt (hrat i).1.le).symm
  have hwpositive:∀S,0<w S:=fun S=>by rw [hw];exact sq_pos_of_pos (hΘ S)
  have hwfactor:∀S,w S=∏i∈bitSupport S,w (unitBit i):=by
    intro S
    have he:=eigenvalue_tensor_identity ρX hXden δX S
    change w S*(w zero)^(Boolean.degree S)=w zero*(∏i∈bitSupport S,w (unitBit i)) at he
    simpa only [hw0,one_pow,mul_one,one_mul] using he
  let D:Matrix (Cube d) (Cube d) ℝ:=Matrix.diagonal (fun S=>(Θ S)⁻¹)
  let O:=D*C
  have hOO:O*O.transpose=1:=by
    apply rowNormalize_orthogonal C Θ (fun S=>(hΘ S).ne')
    rw [hX]
    ext S T
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
    split_ifs
    · exact hw S
    · simp
  have hC:∀S T,C S T=Θ S*O S T:=by
    intro S T
    change C S T=Θ S*(D*C) S T
    rw [Matrix.diagonal_mul]
    simp [D,(hΘ S).ne']
  have hOrow:∀T,O zero T=if T=zero then 1 else 0:=by
    intro T
    change (D*C) zero T=_
    simp only [D,Matrix.diagonal_mul,hΘ0,inv_one,one_mul]
    exact hrow T
  have hOcol:∀S,S≠zero→O S zero=0:=by
    intro S hS
    change (D*C) S zero=0
    simp only [D,Matrix.diagonal_mul]
    rw [hcol,if_neg hS,mul_zero]
  let η:=fun S=>(Θ S)⁻¹*(δ*eigenvalue ρ S)*(Θ S)⁻¹
  have hOZ:O*noiseDiagonal z*O.transpose=Matrix.diagonal η:=by
    change (D*C)*noiseDiagonal z*(D*C).transpose=_
    rw [Matrix.transpose_mul,show D.transpose=D by exact Matrix.diagonal_transpose _]
    calc
      _ = D*(C*noiseDiagonal z*C.transpose)*D:=by simp only [Matrix.mul_assoc]
      _ = _:=by
        rw [hZ]
        ext S T
        simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
        by_cases hst:S=T
        · subst T
          simp only [ite_true]
          rfl
        · simp only [hst,if_false,mul_zero,zero_mul]
  obtain ⟨h,hbound,hsupport,hη⟩:=orthogonal_noise_row_degree O hOO z hz hz1 η hOZ
  have h00:O zero zero=1:=by simpa only [ite_true] using hOrow zero
  obtain ⟨hh0,hsingle⟩:=normalized_degree_zero_and_singletons O hOO h00 hOcol h hsupport
  have hν:∀S,δ*eigenvalue ρ S=w S*z^(h S):=by
    intro S
    have he:=hη S
    dsimp only [η] at he
    rw [hw]
    field_simp [(hΘ S).ne'] at he ⊢
    nlinarith
  have hm:∀S,(w S*z^(h S))*(w zero*z^(h zero))^(Boolean.degree S)=
      (w zero*z^(h zero))*(∏i∈bitSupport S,w (unitBit i)*z^(h (unitBit i))):=by
    intro S
    simp_rw [←hν]
    exact eigenvalue_tensor_identity ρ hρ δ S
  have hdegree:h=Boolean.degree:=weighted_degree_preserved z hz hz1 w hwpositive h hw0 hh0 hwfactor hm hbound hsingle
  refine ⟨θ,hθ,O,hOO,hC,?_,h00,hOcol⟩
  intro S T hne
  by_contra hn
  have he:=hsupport S T hn
  rw [hdegree] at he
  exact hne he.symm

end PlanarHom.RectangularWalshConvolution
