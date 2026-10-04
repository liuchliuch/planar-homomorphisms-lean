import PlanarHom.RectangularWalshCoordinates
import Mathlib.Data.Finset.Max

/-! NEW finite positive-matrix maximum principle and the actual constant-mode
normalization needed by the rectangular Fourier argument. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
variable {C:Type} [Fintype C] [Nonempty C]

theorem positive_rowsum_eigenvector_constant (A:Matrix C C ℝ) (hA:∀i j,0<A i j)
    (lam:ℝ) (hrow:∀i,∑j,A i j=lam) (v:C→ℝ)
    (hv:∀i,∑j,A i j*v j=lam*v i) : ∃c:ℝ,∀i,v i=c := by
  obtain ⟨m,_,hm⟩:=Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  have hn:∀j,0≤A m j*(v m-v j):=fun j=>mul_nonneg (hA m j).le
    (sub_nonneg.mpr (hm j (Finset.mem_univ _)))
  have hz:(∑j,A m j*(v m-v j))=0:=by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hrow,hv]
    ring
  refine ⟨v m,fun i=>?_⟩
  have hi:A m i*(v m-v i)=0:=(Finset.sum_eq_zero_iff_of_nonneg (fun j _=>hn j)).mp hz i (Finset.mem_univ _)
  have hd: v m-v i=0:=(mul_eq_zero.mp hi).resolve_left (hA m i).ne'
  linarith

theorem positive_eigenvalue_eq_of_column_sum (A:Matrix C C ℝ) (lam μ:ℝ)
    (hcol:∀j,∑i,A i j=lam) (v:C→ℝ) (hpos:∀i,0<v i)
    (hv:∀i,∑j,A i j*v j=μ*v i) : lam=μ := by
  have hs:0<∑i,v i:=Finset.sum_pos (fun i _=>hpos i) Finset.univ_nonempty
  apply (mul_right_cancel₀ hs.ne')
  calc
    lam*(∑i,v i)=∑j,(∑i,A i j)*v j:=by simp only [hcol,Finset.mul_sum]
    _ = ∑i,∑j,A i j*v j:=by simp only [Finset.sum_mul];rw [Finset.sum_comm]
    _ = μ*(∑i,v i):=by simp only [hv,Finset.mul_sum]

def rowSum (B:Matrix C C ℝ) (i:C) : ℝ:=∑j,B i j

theorem gram_rowSum_eigenvector (B:Matrix C C ℝ) (lam:ℝ)
    (h:∀i,rowSum (B.transpose*B) i=lam) :
    ∀i,∑j,(B*B.transpose) i j*rowSum B j=lam*rowSum B i := by
  have hg:(B.transpose*B).mulVec (fun _=>1)=fun _=>lam:=by
    funext i
    simpa only [Matrix.mulVec, dotProduct,mul_one,rowSum] using h i
  have he:(B*B.transpose).mulVec (B.mulVec (fun _=>1))=
      B.mulVec ((B.transpose*B).mulVec (fun _=>1)):=by
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [hg] at he
  intro i
  have hei:=congrFun he i
  simpa only [Matrix.mulVec,dotProduct,mul_one,rowSum,Finset.mul_sum,mul_comm] using hei

/-- Positive square matrices with constant-sum Grams have the same positive
row and column sum. No Perron eigenbasis is assumed. -/
theorem gram_constant_mode (B:Matrix C C ℝ) (hB:∀i j,0<B i j)
    (lamX lamY:ℝ) (hX:∀i,rowSum (B*B.transpose) i=lamX)
    (hY:∀i,rowSum (B.transpose*B) i=lamY) :
    ∃s0:ℝ,0<s0 ∧ (∀i,rowSum B i=s0) ∧ (∀i,rowSum B.transpose i=s0) ∧
      lamX=s0^2 ∧ lamY=s0^2 := by
  have hGX:∀i j,0<(B*B.transpose) i j:=fun i j=>
    Finset.sum_pos (fun k _=>mul_pos (hB i k) (hB j k)) Finset.univ_nonempty
  have hGY:∀i j,0<(B.transpose*B) i j:=fun i j=>
    Finset.sum_pos (fun k _=>mul_pos (hB k i) (hB k j)) Finset.univ_nonempty
  have hr:∀i,0<rowSum B i:=fun i=>Finset.sum_pos (fun j _=>hB i j) Finset.univ_nonempty
  have hc:∀i,0<rowSum B.transpose i:=fun i=>Finset.sum_pos (fun j _=>hB j i) Finset.univ_nonempty
  have hcol:∀j,∑i,(B*B.transpose) i j=lamX:=by
    intro j
    have he:∀i,(B*B.transpose) i j=(B*B.transpose) j i:=by
      intro i
      simp only [Matrix.mul_apply,Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simpa only [he] using hX j
  have hlam:lamX=lamY:=positive_eigenvalue_eq_of_column_sum (B*B.transpose) lamX lamY hcol
    (rowSum B) hr (gram_rowSum_eigenvector B lamY hY)
  obtain ⟨s0,hs⟩:=positive_rowsum_eigenvector_constant (B*B.transpose) hGX lamX hX (rowSum B)
    (by simpa only [hlam] using gram_rowSum_eigenvector B lamY hY)
  have hte:=gram_rowSum_eigenvector B.transpose lamX
    (by simpa only [Matrix.transpose_transpose] using hX)
  obtain ⟨t0,ht⟩:=positive_rowsum_eigenvector_constant (B.transpose*B) hGY lamY hY (rowSum B.transpose)
    (by simpa only [Matrix.transpose_transpose,hlam] using hte)
  have hst:s0=t0:=by
    have hsum:(∑i,rowSum B i)=∑i,rowSum B.transpose i:=by
      unfold rowSum
      rw [Finset.sum_comm]
      rfl
    simp only [hs,ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α:=C))) hsum
  have hspos:0<s0:=by
    let i:C:=Classical.choice inferInstance
    rw [←hs i]
    exact hr i
  have hXval:lamX=s0^2:=by
    let i:C:=Classical.choice inferInstance
    calc
      lamX=rowSum (B*B.transpose) i:=(hX i).symm
      _ = ∑k,B i k*rowSum B.transpose k:=by
        simp only [rowSum,Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = s0^2:=by
        simp only [ht,←hst,←Finset.sum_mul]
        change rowSum B i*s0=s0^2
        rw [hs,pow_two]
  exact ⟨s0,hspos,hs,fun i=>(ht i).trans hst.symm,hXval,hlam.symm.trans hXval⟩

end PlanarHom.RectangularWalshConvolution
