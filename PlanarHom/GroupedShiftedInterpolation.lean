import PlanarHom.GroupedProductInterpolation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Add a zero node with zero target value. The resulting grouped projector
has zero constant coefficient, so only positive oracle powers are queried. -/
noncomputable section
open Classical
open scoped BigOperators Polynomial
namespace PlanarHom.GroupedProductInterpolation
variable {I C R : Type} [Fintype I] [Fintype C] [CommRing R]

def zeroNodes (μ : I→R) : Option I→R:=fun i=>i.elim 0 μ
def zeroTargets (η : C→R) : Option C→R:=fun c=>c.elim 0 η

theorem zero_cross_units (group : I→C) (μ : I→R)
    (hμ : ∀i,IsUnit (μ i)) (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) :
    ∀i j,Option.map group i≠Option.map group j→IsUnit (zeroNodes μ i-zeroNodes μ j) := by
  intro i j h
  cases i with
  | none=>
    cases j with
    | none=>exact False.elim (h rfl)
    | some j=>simpa [zeroNodes] using (hμ j).neg
  | some i=>
    cases j with
    | none=>simpa [zeroNodes] using hμ i
    | some j=>
      apply hu i j
      intro he
      exact h (congrArg some he)

def shiftedInterpolant (group : I→C) (μ : I→R) (η : C→R) : Polynomial R:=
  interpolant (Option.map group) (zeroNodes μ) (zeroTargets η)

theorem shiftedInterpolant_eval (group : I→C) (μ : I→R) (η : C→R)
    (hμ : ∀i,IsUnit (μ i)) (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) (i : I) :
    (shiftedInterpolant group μ η).eval (μ i)=η (group i) :=
  interpolant_eval _ _ _ (zero_cross_units group μ hμ hu) (some i)

theorem shiftedInterpolant_zero (group : I→C) (μ : I→R) (η : C→R)
    (hμ : ∀i,IsUnit (μ i)) (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) :
    (shiftedInterpolant group μ η).coeff 0=0 := by
  have h:=interpolant_eval (Option.map group) (zeroNodes μ) (zeroTargets η)
    (zero_cross_units group μ hμ hu) none
  simpa [shiftedInterpolant,zeroNodes,zeroTargets,Polynomial.coeff_zero_eq_eval_zero] using h

theorem shiftedInterpolant_degree [Nontrivial R] (group : I→C) (μ : I→R) (η : C→R) :
    (shiftedInterpolant group μ η).natDegree≤(Fintype.card I+1)*(Fintype.card I+2) := by
  simpa [shiftedInterpolant,add_assoc] using interpolant_degree (Option.map group) (zeroNodes μ) (zeroTargets η)

/-- Actual coefficient-dot-positive-query recovery, with arbitrary signed
contraction weights and any number of repeated nodes within a target group. -/
theorem recover_positive_moments [Nontrivial R] {A : Type} [Fintype A]
    (group : I→C) (μ : I→R) (η : C→R) (hμ : ∀i,IsUnit (μ i))
    (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j))
    (node : A→I) (weight : A→R) :
    let D:=(Fintype.card I+1)*(Fintype.card I+2)
    (∑n∈Finset.range D,(shiftedInterpolant group μ η).coeff (n+1)*
      (∑a,weight a*μ (node a)^(n+1)))=∑a,weight a*η (group (node a)) := by
  dsimp only
  let P:=shiftedInterpolant group μ η
  let D:=(Fintype.card I+1)*(Fintype.card I+2)
  have hdegree:P.natDegree<D+1:=Nat.lt_succ_of_le (shiftedInterpolant_degree group μ η)
  have hzero:P.coeff 0=0:=shiftedInterpolant_zero group μ η hμ hu
  have heval (i : I) : (∑n∈Finset.range D,P.coeff (n+1)*μ i^(n+1))=η (group i) := by
    have h:=Polynomial.eval_eq_sum_range' (p:=P) hdegree (μ i)
    rw [Finset.sum_range_succ'] at h
    simp only [hzero,zero_mul,add_zero] at h
    exact h.symm.trans (shiftedInterpolant_eval group μ η hμ hu i)
  change (∑n∈Finset.range D,P.coeff (n+1)*(∑a,weight a*μ (node a)^(n+1)))=_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←heval (node a),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end PlanarHom.GroupedProductInterpolation
