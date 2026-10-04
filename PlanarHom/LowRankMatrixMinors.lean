import PlanarHom.PositiveRankOneAmplitudes

/-! NEW literal rectangular low-rank/minor interface for the support-component
rank condition in Proposition 2.5. No positivity or algorithmic premise enters. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
variable {C D E F:Type} [Fintype C] [Fintype D] [Fintype E] [Fintype F]

 theorem rectangular_rank_submatrix_le (M:Matrix C D ℝ) (f:E→C) (g:F→D) :
    (M.submatrix f g).rank≤M.rank := by
  let B:=M.submatrix f (Equiv.refl D)
  have h1:B.rank≤M.rank:=Matrix.rank_submatrix_le f (Equiv.refl D) M
  have h2:(B.transpose.submatrix g (Equiv.refl E)).rank≤B.transpose.rank:=
    Matrix.rank_submatrix_le g (Equiv.refl E) B.transpose
  have he:(M.submatrix f g).transpose=B.transpose.submatrix g (Equiv.refl E):=rfl
  calc
    _ = (M.submatrix f g).transpose.rank := (Matrix.rank_transpose _).symm
    _ = _ := congrArg Matrix.rank he
    _ ≤ B.transpose.rank := h2
    _ = B.rank := Matrix.rank_transpose _
    _ ≤ M.rank := h1

 theorem rank_pos_of_entry_ne_zero (M:Matrix C D ℝ) (i:C) (j:D) (h:M i j≠0) : 0<M.rank := by
  let A:Matrix (Fin 1) (Fin 1) ℝ:=M.submatrix (fun _=>i) (fun _=>j)
  have hd:A.det≠0:=by simpa [A,Matrix.det_fin_one,Matrix.submatrix_apply] using h
  have hr:=Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd))
  have hl:=rectangular_rank_submatrix_le M (fun _:Fin 1=>i) (fun _:Fin 1=>j)
  change A.rank≤M.rank at hl
  simp only [Fintype.card_fin] at hr
  omega

 theorem matrix_zero_of_rank_zero (M:Matrix C D ℝ) (h:M.rank=0) : M=0 := by
  ext i j
  by_contra hn
  have hh:=rank_pos_of_entry_ne_zero M i j hn
  omega

 theorem exists_nonzero_entry_of_rank_one (M:Matrix C D ℝ) (h:M.rank=1) : ∃i j,M i j≠0 := by
  by_contra hn
  have hz:M=0:=by ext i j;exact not_ne_iff.mp (fun hij=>hn ⟨i,j,hij⟩)
  rw [hz,Matrix.rank_zero] at h
  contradiction

 theorem rectangular_minor_zero_of_rank_le_one (M:Matrix C D ℝ) (hr:M.rank≤1) (i r:C) (j s:D) :
    M i j*M r s=M i s*M r j := by
  let f:Fin 2→C:=fun t=>if t=0 then i else r
  let g:Fin 2→D:=fun t=>if t=0 then j else s
  let A:=M.submatrix f g
  have hA:A.rank≤1:=(rectangular_rank_submatrix_le M f g).trans hr
  have hd:A.det=0:=by
    by_contra hn
    have hu:IsUnit A:=(Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hn)
    have hh:=Matrix.rank_of_isUnit A hu
    simp only [Fintype.card_fin] at hh
    omega
  rw [Matrix.det_fin_two] at hd
  have hh:M i j*M r s-M i s*M r j=0:=by simpa [A,Matrix.submatrix_apply,f,g] using hd
  exact sub_eq_zero.mp hh

 theorem symmetric_rank_one_nonzero_diagonal (M:Matrix C C ℝ) (hs:∀i j,M i j=M j i) (hr:M.rank=1) :
    ∃r,M r r≠0 := by
  obtain ⟨i,j,hn⟩:=exists_nonzero_entry_of_rank_one M hr
  refine ⟨i,?_⟩
  intro hi
  have hh:=two_minor_zero_of_rank_le_one M (by omega) i i j
  rw [hi,zero_mul,hs j i] at hh
  exact (mul_ne_zero hn hn) hh.symm

end PlanarHom.GadgetDiagonalSeparation
