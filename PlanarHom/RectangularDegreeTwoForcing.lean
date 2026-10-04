import PlanarHom.RectangularLinearConvolution
import PlanarHom.RectangularSignedPermutation
import PlanarHom.RectangularSourceNormData

/-! NEW degree-two equality forcing the actual singleton orthogonal block to
be a signed coordinate permutation. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

def singletonMatrix (O:Matrix (Cube d) (Cube d) ℝ):Matrix (Fin d) (Fin d) ℝ:=
  fun i j=>O (unitBit i) (unitBit j)

theorem singleton_orthogonal (O:Matrix (Cube d) (Cube d) ℝ) (hO:O*O.transpose=1)
    (hdeg:∀S T,Boolean.degree S≠Boolean.degree T→O S T=0):
    singletonMatrix O*(singletonMatrix O).transpose=1:=by
  ext i k
  have he:=congrFun (congrFun hO (unitBit i)) (unitBit k)
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] at he ⊢
  rw [sum_degree_one (fun T=>O (unitBit i) T*O (unitBit k) T) (by
    intro T hT
    dsimp only
    rw [hdeg (unitBit i) T (by rw [degree_unitBit];exact hT.symm),zero_mul])] at he
  simpa only [singletonMatrix,unitBit_injective.eq_iff] using he

@[simp] theorem characterWeight_pair (θ:Fin d→ℝ) (i k:Fin d) (hik:i≠k):
    characterWeight θ (pairBits i k)=θ i*θ k:=by
  rw [characterWeight,support_pairBits,Finset.prod_pair hik]

theorem pair_block_coefficient (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (i k:Fin d) (hik:i≠k) (T:Cube d):
    (squareCoefficientPolynomial C (pairBits i k) T).coeff 2=
      (2*(θ i*θ k))*(O (pairBits i k) T+rowConvolution (O (unitBit i)) (O (unitBit k)) T):=by
  rw [squareCoefficient_pair C hrow i k hik T,hrep,characterWeight_pair θ i k hik]
  have hc:rowConvolution (C (unitBit i)) (C (unitBit k)) T=
      (θ i*θ k)*rowConvolution (O (unitBit i)) (O (unitBit k)) T:=by
    unfold rowConvolution
    simp_rw [hrep,characterWeight_singleton]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw [hc]
  ring

theorem singleton_disjoint_of_norms (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hθ:∀i,0<θ i) (hO:O*O.transpose=1)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hdeg:∀S T,Boolean.degree S≠Boolean.degree T→O S T=0)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hnorm:∀S,(∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(characterWeight θ S)^2):
    ∀i k,i≠k→∀j,singletonMatrix O i j*singletonMatrix O k j=0:=by
  intro i k hik
  let u:=O (unitBit i)
  let v:=O (unitBit k)
  let r:=O (pairBits i k)
  have hu:∀S,Boolean.degree S≠1→u S=0:=fun S h=>hdeg (unitBit i) S (by rw [degree_unitBit];exact h.symm)
  have hv:∀S,Boolean.degree S≠1→v S=0:=fun S h=>hdeg (unitBit k) S (by rw [degree_unitBit];exact h.symm)
  have hU:=singleton_orthogonal O hO hdeg
  have hdot:(∑j:Fin d,u (unitBit j)*v (unitBit j))=0:=by
    have he:=congrFun (congrFun hU i) k
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_ne hik,singletonMatrix] using he
  have hun:(∑j:Fin d,u (unitBit j)^2)=1:=by
    have he:=congrFun (congrFun hU i) i
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,singletonMatrix,pow_two] using he
  have hvn:(∑j:Fin d,v (unitBit j)^2)=1:=by
    have he:=congrFun (congrFun hU k) k
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,singletonMatrix,pow_two] using he
  have hconv:=linear_convolution_norm u v hu hv hdot
  rw [hun,hvn] at hconv
  have hnonneg:0≤∑j:Fin d,u (unitBit j)^2*v (unitBit j)^2:=
    Finset.sum_nonneg (fun j _=>mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hshort:(∑T:Cube d,rowConvolution u v T^2)≤1:=by nlinarith
  have hmax:(∑T:Cube d,(r T+rowConvolution u v T)^2)=4:=by
    have he:=hnorm (pairBits i k)
    rw [pairBits_degree i k hik,characterWeight_pair θ i k hik] at he
    simp_rw [pair_block_coefficient C O θ hrep hrow i k hik,mul_pow] at he
    rw [←Finset.mul_sum] at he
    have ha:(2*(θ i*θ k))^2≠0:=pow_ne_zero 2 (mul_ne_zero (by norm_num) (mul_ne_zero (hθ i).ne' (hθ k).ne'))
    apply mul_left_cancel₀ ha
    calc
      _=4^2*(θ i*θ k)^2:=by simpa only [mul_pow,u,v,r] using he
      _=_:=by ring
  have hconvone:(∑T:Cube d,rowConvolution u v T^2)=1:=
    (unit_plus_short_max r (rowConvolution u v) (orthogonal_row_norm O hO _) hshort hmax).1
  have hz:(∑j:Fin d,u (unitBit j)^2*v (unitBit j)^2)=0:=by nlinarith
  intro j
  have hj:u (unitBit j)^2*v (unitBit j)^2=0:=(Finset.sum_eq_zero_iff_of_nonneg
    (fun k _=>mul_nonneg (sq_nonneg (u (unitBit k))) (sq_nonneg (v (unitBit k))))).mp hz j (Finset.mem_univ _)
  change u (unitBit j)*v (unitBit j)=0
  nlinarith [sq_nonneg (u (unitBit j)*v (unitBit j))]

theorem singleton_signed_permutation_of_norms (C O:Matrix (Cube d) (Cube d) ℝ) (θ:Fin d→ℝ)
    (hθ:∀i,0<θ i) (hO:O*O.transpose=1)
    (hrep:∀S T,C S T=characterWeight θ S*O S T)
    (hdeg:∀S T,Boolean.degree S≠Boolean.degree T→O S T=0)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hnorm:∀S,(∑T:Cube d,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2)=
      4^(Boolean.degree S)*(characterWeight θ S)^2):
    ∃p:Fin d≃Fin d,∃flip:Fin d→Bool,∀i j,
      O (unitBit i) (unitBit j)=if j=p i then signValue (flip i) else 0:=
  orthogonal_disjoint_signed_permutation (singletonMatrix O) (singleton_orthogonal O hO hdeg)
    (singleton_disjoint_of_norms C O θ hθ hO hrep hdeg hrow hnorm)

end PlanarHom.RectangularWalshConvolution
