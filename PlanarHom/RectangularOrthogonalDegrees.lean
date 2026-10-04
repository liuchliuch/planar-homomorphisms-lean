import PlanarHom.RectangularWalshCoordinates

/-! NEW exact degree-support consequences of diagonal orthogonal conjugation.
The finite degree arithmetic is separate from the actual Gram instantiation. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
variable {C:Type} [Fintype C] [DecidableEq C]

theorem orthogonal_row_nonzero (O:Matrix C C ℝ) (hO:O*O.transpose=1) (i:C) :
    ∃j,O i j≠0 := by
  by_contra h
  push_neg at h
  have hi:=congrFun (congrFun hO i) i
  simp only [Matrix.mul_apply,Matrix.transpose_apply,h,zero_mul,Finset.sum_const_zero,Matrix.one_apply_eq] at hi
  norm_num at hi

theorem orthogonal_diagonal_support (O:Matrix C C ℝ) (hO:O*O.transpose=1)
    (lam μ:C→ℝ) (hd:O*Matrix.diagonal lam*O.transpose=Matrix.diagonal μ)
    (i j:C) (hij:O i j≠0) : lam j=μ i := by
  have hOt:O.transpose*O=1:=Matrix.mul_eq_one_comm.mp hO
  have he:=congrArg (fun A:Matrix C C ℝ=>A*O) hd
  simp only [Matrix.mul_assoc,hOt,Matrix.mul_one] at he
  have hv:=congrFun (congrFun he i) j
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at hv
  exact (mul_left_cancel₀ hij) (hv.trans (mul_comm _ _))

theorem orthogonal_noise_row_degree {d:ℕ} (O:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (hO:O*O.transpose=1) (z:ℝ) (hz:0<z) (hz1:z<1) (μ:Boolean.Cube d→ℝ)
    (hd:O*noiseDiagonal z*O.transpose=Matrix.diagonal μ) :
    ∃h:Boolean.Cube d→ℕ,(∀S,h S≤d) ∧
      (∀S T,O S T≠0→Boolean.degree T=h S) ∧ (∀S,μ S=z^(h S)) := by
  choose index hindex using orthogonal_row_nonzero O hO
  let h:=fun S=>Boolean.degree (index S)
  refine ⟨h,?_,?_,?_⟩
  · intro S
    unfold h Boolean.degree
    calc
      _ ≤ ∑i:Fin d,1:=Finset.sum_le_sum (fun i _=>by split <;> norm_num)
      _ = d:=by simp
  · intro S T hST
    apply pow_right_injective₀ hz hz1.ne
    exact (orthogonal_diagonal_support O hO _ μ hd S T hST).trans
      (orthogonal_diagonal_support O hO _ μ hd S (index S) (hindex S)).symm
  · intro S
    exact (orthogonal_diagonal_support O hO _ μ hd S (index S) (hindex S)).symm

theorem additive_degree_is_card {d:ℕ} (h:Boolean.Cube d→ℕ)
    (hadd:∀S,h S=∑i:Fin d,if S i then h (Boolean.unitBit i) else 0)
    (hbound:∀S,h S≤d) (hpos:∀i,1≤h (Boolean.unitBit i)) : h=Boolean.degree := by
  have hsum:(∑i:Fin d,h (Boolean.unitBit i))≤d:=by
    have hf:=hbound (fun _=>true)
    rw [hadd] at hf
    simpa only [ite_true] using hf
  have hall:∀i,h (Boolean.unitBit i)=1:=by
    have he:(∑i:Fin d,h (Boolean.unitBit i))=∑i:Fin d,1:=by
      apply le_antisymm
      · simpa using hsum
      · exact Finset.sum_le_sum (fun i _=>hpos i)
    have hz:(∑i:Fin d,(h (Boolean.unitBit i)-1))=0:=by
      rw [Finset.sum_tsub_distrib Finset.univ (fun i _=>hpos i),he,Nat.sub_self]
    intro i
    have hi:=Finset.sum_eq_zero_iff.mp hz i (Finset.mem_univ _)
    have :=hpos i
    omega
  funext S
  rw [hadd]
  simp only [hall,Boolean.degree]

end PlanarHom.RectangularWalshConvolution
