import PlanarHom.RankOneRealTractability
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! NEW actual positive symmetric rank-one factorization from vanishing
literal two-by-two minors, with no spectral or source-code oracle. -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
variable {C D E:Type} [Fintype C] [Fintype D] [Fintype E]

 theorem rank_submatrix_both (M:Matrix C C ℝ) (f:D→C) (g:E→C) :
    (M.submatrix f g).rank≤M.rank := by
  let B:=M.submatrix f (Equiv.refl C)
  have h1:B.rank≤M.rank:=Matrix.rank_submatrix_le f (Equiv.refl C) M
  have h2:(B.transpose.submatrix g (Equiv.refl D)).rank≤B.transpose.rank:=
    Matrix.rank_submatrix_le g (Equiv.refl D) B.transpose
  have he:(M.submatrix f g).transpose=B.transpose.submatrix g (Equiv.refl D):=rfl
  calc
    _ = (M.submatrix f g).transpose.rank := (Matrix.rank_transpose _).symm
    _ = _ := congrArg Matrix.rank he
    _ ≤ B.transpose.rank := h2
    _ = B.rank := Matrix.rank_transpose _
    _ ≤ M.rank := h1

 theorem two_minor_zero_of_rank_le_one (M:Matrix C C ℝ) (hr:M.rank≤1) (i j r:C) :
    M i j*M r r=M i r*M r j := by
  let f:Fin 2→C:=fun t=>if t=0 then i else r
  let g:Fin 2→C:=fun t=>if t=0 then j else r
  let A:=M.submatrix f g
  have hA:A.rank≤1:=(rank_submatrix_both M f g).trans hr
  have hd:A.det=0:=by
    by_contra hn
    have hu:IsUnit A:=(Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hn)
    have hh:=Matrix.rank_of_isUnit A hu
    simp only [Fintype.card_fin] at hh
    omega
  rw [Matrix.det_fin_two] at hd
  have hh:M i j*M r r-M i r*M r j=0:=by simpa [A,Matrix.submatrix_apply,f,g] using hd
  exact sub_eq_zero.mp hh

 theorem positive_amplitudes_of_rank_le_one (M:Matrix C C ℝ) (r:C)
    (hs:∀i j,M i j=M j i) (hp:∀i j,0<M i j) (hr:M.rank≤1) :
    ∃a:C→ℝ,(∀i,0<a i) ∧ ∀i j,M i j=a i*a j := by
  let a:=fun i=>M i r/Real.sqrt (M r r)
  refine ⟨a,fun i=>div_pos (hp i r) (Real.sqrt_pos.mpr (hp r r)),?_⟩
  intro i j
  calc
    M i j = M i r*M r j/M r r := (eq_div_iff (hp r r).ne').mpr (two_minor_zero_of_rank_le_one M hr i j r)
    _ = a i*a j := by
      rw [hs r j]
      dsimp only [a]
      rw [div_mul_div_comm,Real.mul_self_sqrt (hp r r).le]

end PlanarHom.GadgetDiagonalSeparation
