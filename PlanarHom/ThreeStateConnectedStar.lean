import PlanarHom.ThreeStatePositiveRank
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The connected nonnegative three-state specialization needed by the signed
three-state argument. Irreducibility is stated as the absence of a nonconstant
Boolean zero-cut; no graph algorithm or planarity premise is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.ThreeStateDimension
open Structures Boolean

def starMatrix (a b:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,a;0,0,b;a,b,0]

def NoBooleanZeroCut {C:Type} (M:Matrix C C ℝ) : Prop :=
  ∀f:C→Bool,(∀i j,f i≠f j→M i j=0)→∀i j,f i=f j

theorem class_allowed_of_noBooleanZeroCut {C:Type} [Nonempty C]
    {M:Matrix C C ℝ} (hirr:NoBooleanZeroCut M) (h:NonnegativeClass M) : AllowedBlock M := by
  obtain ⟨t,b,hb,hz,ha⟩:=h
  let c:C:=Classical.choice inferInstance
  let f:C→Bool:=fun i=>decide (b i=b c)
  have hf : ∀i j,f i≠f j→M i j=0 := by
    intro i j he
    exact hz i j (fun hh=>he (by simp only [f,hh]))
  have hc : ∀i,b i=b c := by
    intro i
    have hh:=hirr f hf i c
    have he:decide (b i=b c)=true:=by simpa only [f,decide_true] using hh
    exact of_decide_eq_true he
  let e:C≃{i//b i=b c} := {
    toFun:=fun i=>⟨i,hc i⟩
    invFun:=Subtype.val
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (ha (b c)).equiv e

theorem bipartite_two_one_star (a:Fin 2→ℝ) (b:Fin 1→ℝ)
    (i j:Fin 2⊕Fin 1) :
    bipartiteAmplitude a b i j=starMatrix (a 0*b 0) (a 1*b 0)
      (finSumFinEquiv i) (finSumFinEquiv j) := by
  cases i with
  | inl i=>cases j with
    | inl j=>fin_cases i <;> fin_cases j <;> rfl
    | inr j=>fin_cases i <;> fin_cases j <;> rfl
  | inr i=>cases j with
    | inl j=>fin_cases i <;> fin_cases j <;> rfl
    | inr j=>fin_cases i <;> fin_cases j <;> rfl

theorem bipartite_swap_amplitude {k l:ℕ} (a:Fin k→ℝ) (b:Fin l→ℝ)
    (i j:Fin k⊕Fin l) :
    bipartiteAmplitude a b i j=
      bipartiteAmplitude b a ((Equiv.sumComm _ _) i) ((Equiv.sumComm _ _) j) := by
  cases i <;> cases j <;> simp [bipartiteAmplitude,mul_comm]

theorem allowed_three_rank_or_star {M:Matrix (Fin 3) (Fin 3) ℝ} (h:AllowedBlock M) :
    M.rank≤1 ∨ ∃(a b:ℝ)(e:Equiv.Perm (Fin 3)),0<a ∧ 0<b ∧
      ∀i j,M i j=starMatrix a b (e i) (e j) := by
  cases h with
  | zero e hz=>
    have he:=Fintype.card_congr e
    norm_num at he
  | positive k d hk a ρ ha hρ e hm=>
    left
    have hp : ∀i j,0<M i j := by
      intro i j; rw [hm]; exact mul_pos (mul_pos (ha _) (ha _)) (tensor_pos hρ _ _)
    exact positive_allowed_rank_le_one (Fintype.card_fin 3) hp
      (.positive k d hk a ρ ha hρ e hm)
  | bipartite k l d hk hl a b ρ ha hb hρ e hm=>
    right
    have hcard : (k+l)*2^d=3 := by
      have he:=Fintype.card_congr e
      simpa [Cube] using he.symm
    have hd:=odd_three_dimension hcard
    subst d
    have hkl : k+l=3 := by simpa using hcard
    have hcases : (k=2 ∧ l=1) ∨ (k=1 ∧ l=2) := by omega
    rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · let ep:Equiv.Perm (Fin 3) := e.trans (Equiv.prodUnique _ _) |>.trans finSumFinEquiv
      refine ⟨a 0*b 0,a 1*b 0,ep,mul_pos (ha 0) (hb 0),mul_pos (ha 1) (hb 0),?_⟩
      intro i j
      rw [hm,tensor_empty,mul_one]
      exact bipartite_two_one_star a b (e i).1 (e j).1
    · let ep:Equiv.Perm (Fin 3) := e.trans (Equiv.prodUnique _ _) |>.trans
        ((Equiv.sumComm _ _).trans finSumFinEquiv)
      refine ⟨b 0*a 0,b 1*a 0,ep,mul_pos (hb 0) (ha 0),mul_pos (hb 1) (ha 0),?_⟩
      intro i j
      rw [hm,tensor_empty,mul_one,bipartite_swap_amplitude]
      exact bipartite_two_one_star b a ((Equiv.sumComm _ _) (e i).1) ((Equiv.sumComm _ _) (e j).1)

theorem nonnegativeClass_three_rank_or_star {M:Matrix (Fin 3) (Fin 3) ℝ}
    (hirr:NoBooleanZeroCut M) (h:NonnegativeClass M) :
    M.rank≤1 ∨ ∃(a b:ℝ)(e:Equiv.Perm (Fin 3)),0<a ∧ 0<b ∧
      ∀i j,M i j=starMatrix a b (e i) (e j) :=
  allowed_three_rank_or_star (class_allowed_of_noBooleanZeroCut hirr h)

end PlanarHom.ThreeStateDimension
