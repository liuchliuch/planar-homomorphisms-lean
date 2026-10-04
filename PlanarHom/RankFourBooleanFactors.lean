import PlanarHom.RankFourSingleBlock

/-! The original Boolean equation (2.3), restricted to nonnegative entries.
A full-rank tensor cannot contain its rank-one branch. -/
noncomputable section
open Classical
namespace PlanarHom.RankFour
open Boolean

/-- Equation (2.3) for a symmetric nonnegative Boolean matrix. The signed
fourth branch is redundant on nonnegative entries. -/
def BooleanEasy (A : Matrix Bool Bool ℝ) : Prop :=
  (∀i j,A i j=A j i) ∧ (∀i j,0≤A i j) ∧
    (A false false*A true true=A false true^2 ∨
      A false true=0 ∨ A false false=A true true)

def factorProduct (A B : Matrix Bool Bool ℝ) : Matrix (Bool×Bool) (Bool×Bool) ℝ :=
  fun i j=>A i.1 j.1*B i.2 j.2

theorem tensor_factor_not_rankOne {C : Type} {M : Matrix C C ℝ}
    (hi : LinearIndependent ℝ M) (A B : Matrix Bool Bool ℝ)
    (hs : ∀i j,A i j=A j i) (e:C≃Bool×Bool)
    (hm : ∀i j,M i j=factorProduct A B (e i) (e j)) :
    A false false*A true true≠A false true^2 := by
  intro hr
  by_cases ha : A false false=0
  · have hb : A false true=0 := by
      have hz : A false true^2=0 := by simpa [ha] using hr.symm
      exact sq_eq_zero_iff.mp hz
    have hz : M (e.symm (false,false))=0 := by
      funext j
      rw [hm]
      simp only [factorProduct,Equiv.apply_symm_apply]
      cases (e j).1 <;> simp [ha,hb]
    exact LinearIndependent.ne_zero (e.symm (false,false)) hi hz
  · have hh : e.symm (true,false)=e.symm (false,false) := by
      apply hi.eq_of_smul_apply_eq_smul_apply (A false false) (A false true) _ _ ha
      funext j
      simp only [Pi.smul_apply,smul_eq_mul,hm,factorProduct,Equiv.apply_symm_apply]
      cases (e j).1
      · rw [hs true false]; ring
      · calc
          _ = (A false false*A true true)*B false (e j).2 := by ring
          _ = _ := by rw [hr]; ring
    have := congrArg Prod.fst (e.symm.injective hh)
    contradiction

/-- Every invertible nonnegative tractable Boolean factor is positive
diagonal, a positive swap, or a positive scalar zero-field interaction. -/
inductive BooleanNormal (A : Matrix Bool Bool ℝ) : Prop
  | diagonal (a c:ℝ) (ha:0<a) (hc:0<c)
      (h:∀i j,A i j=if i=j then (if i then c else a) else 0)
  | swap (γ:ℝ) (hγ:0<γ) (h:∀i j,A i j=γ*RankFour.swap i j)
  | ising (γ ρ:ℝ) (hγ:0<γ) (hρ:0<ρ) (h:∀i j,A i j=γ*W ρ i j)

theorem boolean_normal {A : Matrix Bool Bool ℝ} (h:BooleanEasy A)
    (hr:A false false*A true true≠A false true^2) : BooleanNormal A := by
  obtain ⟨hs,hn,hcase⟩:=h
  by_cases hb0 : A false true=0
  · have ha : 0<A false false := by
      have:=hn false false
      by_contra hh
      have hz:A false false=0:=by linarith
      exact hr (by simp [hz,hb0])
    have hc : 0<A true true := by
      have:=hn true true
      by_contra hh
      have hz:A true true=0:=by linarith
      exact hr (by simp [hz,hb0])
    refine .diagonal _ _ ha hc ?_
    intro i j; cases i <;> cases j <;> simp [hb0,hs true false]
  · have hd : A false false=A true true := hcase.resolve_left hr |>.resolve_left hb0
    have hb : 0<A false true := lt_of_le_of_ne (hn false true) (Ne.symm hb0)
    by_cases ha : A false false=0
    · refine .swap _ hb ?_
      intro i j; cases i <;> cases j <;> simp [swap,ha,←hd,hs true false]
    · have hapos : 0<A false false := lt_of_le_of_ne (hn false false) (Ne.symm ha)
      refine .ising (A false false) (A false true/A false false) hapos (div_pos hb hapos) ?_
      intro i j; cases i <;> cases j <;> simp [W,←hd,hs true false] <;> field_simp

end PlanarHom.RankFour
