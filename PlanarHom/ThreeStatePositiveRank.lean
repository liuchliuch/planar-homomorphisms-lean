import PlanarHom.RankFourStructuralTransport
import PlanarHom.RankFourAllowedDimensions

/-! The odd three-state cardinality eliminates every Ising coordinate in a
strictly positive tractable block. The remaining matrix is literally an outer
product, so its matrix rank is at most one. -/
noncomputable section
open Classical
namespace PlanarHom.ThreeStateDimension
open Structures Boolean

theorem odd_three_dimension {k d:ℕ} (h:k*2^d=3) : d=0 := by
  cases d with
  | zero=>rfl
  | succ d=>
    have he : 2*(k*2^d)=3 := by simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using h
    omega

theorem positive_class_allowed {C:Type} [Nonempty C] {M:Matrix C C ℝ}
    (hp:∀i j,0<M i j) (h:NonnegativeClass M) : AllowedBlock M := by
  obtain ⟨t,b,hb,hz,ha⟩:=h
  let c:C:=Classical.choice inferInstance
  have hc : ∀i,b i=b c := by
    intro i
    by_contra he
    have:=hz i c he
    linarith [hp i c]
  let e : C≃{i//b i=b c} := {
    toFun:=fun i=>⟨i,hc i⟩
    invFun:=Subtype.val
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (ha (b c)).equiv e

theorem positive_allowed_rank_le_one {C:Type} [Fintype C] [Nonempty C]
    {M:Matrix C C ℝ} (hc:Fintype.card C=3)
    (hp:∀i j,0<M i j) (h:AllowedBlock M) : M.rank≤1 := by
  cases h with
  | zero e hz=>
    let c:C:=Classical.choice inferInstance
    have:=hz c c
    linarith [hp c c]
  | positive k d hk a ρ ha hρ e hm=>
    have hd : d=0 := by
      apply odd_three_dimension
      have he:=Fintype.card_congr e
      simpa [hc,Cube] using he.symm
    subst d
    have he : M=Matrix.vecMulVec (fun i=>a (e i).1) (fun i=>a (e i).1) := by
      funext i j
      simpa only [tensor_empty,mul_one,Matrix.vecMulVec_apply] using hm i j
    rw [he]
    exact Matrix.rank_vecMulVec_le _ _
  | bipartite k l d hk hl a b ρ ha hb hρ e hm=>
    let c:=e.symm (Sum.inl ⟨0,hk⟩,fun _=>false)
    have hz : M c c=0 := by simp [hm,c,bipartiteAmplitude]
    linarith [hp c c]

theorem positive_nonnegativeClass_rank_le_one {M:Matrix (Fin 3) (Fin 3) ℝ}
    (hp:∀i j,0<M i j) (h:NonnegativeClass M) : M.rank≤1 :=
  positive_allowed_rank_le_one (Fintype.card_fin 3) hp (positive_class_allowed hp h)

end PlanarHom.ThreeStateDimension
