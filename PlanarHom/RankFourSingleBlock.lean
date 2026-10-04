import PlanarHom.RankFourAllowedDimensions
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures Boolean

/-- The nonnegative equal-diagonal Boolean interaction with zero diagonal. -/
def swap : Matrix Bool Bool ℝ := fun x y=>if x=y then 0 else 1

def sideEquiv : (Fin 1⊕Fin 1)≃Bool where
  toFun := Sum.elim (fun _=>false) (fun _=>true)
  invFun := fun x=>if x then .inr 0 else .inl 0
  left_inv := by intro x; cases x with
    | inl i => simp [Fin.eq_zero i]
    | inr i => simp [Fin.eq_zero i]
  right_inv := by intro x; cases x <;> rfl

/-- The two possible indecomposable full-rank four-state structural charts. -/
def SingleTensor {C : Type} (M : Matrix C C ℝ) : Prop :=
  (∃(γ:ℝ)(ρ:Fin 2→ℝ)(e:C≃Cube 2),0<γ ∧ (∀r,0<ρ r) ∧
    ∀i j,M i j=γ*tensor ρ (e i) (e j)) ∨
  (∃(γ ρ:ℝ)(e:C≃Bool×Bool),0<γ ∧ 0<ρ ∧
    ∀i j,M i j=γ*swap (e i).1 (e j).1*W ρ (e i).2 (e j).2)

theorem allowedBlock_singleTensor {C : Type} [Fintype C]
    {M : Matrix C C ℝ} (hc : Fintype.card C=4) (hr : M.rank=4)
    (h : AllowedBlock M) : SingleTensor M := by
  have hi := rows_independent (hr.trans hc.symm)
  cases h with
  | zero e hz =>
    have he := Fintype.card_congr e
    simp [hc] at he
  | positive k d hk a ρ ha hρ e hm =>
    have hk1 := positive_amplitude_size hi hk a ρ ha e hm
    subst k
    have hd : d=2 := by
      apply pow_two_eq_four
      have he := Fintype.card_congr e
      simpa [hc,Cube] using he.symm
    subst d
    refine Or.inl ⟨a 0*a 0,ρ,e.trans (Equiv.uniqueProd _ _),mul_pos (ha 0) (ha 0),hρ,?_⟩
    intro i j
    simpa only [Equiv.trans_apply,Equiv.uniqueProd_apply,Fin.eq_zero (e i).1,
      Fin.eq_zero (e j).1] using hm i j
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    obtain ⟨hk1,hl1⟩:=bipartite_amplitude_sizes hi hk hl a b ρ ha hb e hm
    subst k; subst l
    have hd : d=1 := by
      apply twice_pow_two_eq_four
      have he := Fintype.card_congr e
      simpa [hc,Cube] using he.symm
    subst d
    let ep : C≃Bool×Bool := e.trans (Equiv.prodCongr sideEquiv (Equiv.funUnique _ _))
    refine Or.inr ⟨a 0*b 0,ρ 0,ep,mul_pos (ha 0) (hb 0),hρ 0,?_⟩
    intro i j
    rw [hm]
    have ht : tensor ρ (e i).2 (e j).2=W (ρ 0) ((e i).2 0) ((e j).2 0) := by
      simp [tensor]
    rw [ht]
    change bipartiteAmplitude a b (e i).1 (e j).1*_=a 0*b 0*swap _ _*_
    cases hxi:(e i).1 <;> cases hxj:(e j).1 <;>
      simp [ep,sideEquiv,swap,bipartiteAmplitude,hxi,hxj,Fin.eq_zero]

end PlanarHom.RankFour
