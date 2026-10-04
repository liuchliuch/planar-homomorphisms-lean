import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-! Polynomial group projectors with repeated nodes inside each group.
Only cross-group differences must be units. This works in commutative rings
with zero divisors; no field or radical-independence premise is used. -/
noncomputable section
open Classical
open scoped BigOperators Polynomial
namespace PlanarHom.GroupedProductInterpolation
variable {I C R : Type} [Fintype I] [Fintype C] [CommRing R]

def members (group : I→C) (c : C) : Finset I:=Finset.univ.filter (fun i=>group i=c)
def outsiders (group : I→C) (c : C) : Finset I:=Finset.univ.filter (fun i=>group i≠c)
def groupPolynomial (group : I→C) (μ : I→R) (c : C) : Polynomial R:=
  ∏i∈members group c,(Polynomial.X-Polynomial.C (μ i))
def outsidePolynomial (group : I→C) (μ : I→R) (c : C) : Polynomial R:=
  ∏i∈outsiders group c,(Polynomial.X-Polynomial.C (μ i))
def reciprocalFactor (P : Polynomial R) (b : R) : Polynomial R:=
  Polynomial.C (-Ring.inverse (P.eval b))*(P /ₘ (Polynomial.X-Polynomial.C b))
def projector (group : I→C) (μ : I→R) (c : C) : Polynomial R:=
  outsidePolynomial group μ c * ∏j∈outsiders group c,reciprocalFactor (groupPolynomial group μ c) (μ j)

theorem quotient_eval (P : Polynomial R) (a b : R) :
    (a-b)*(P /ₘ (Polynomial.X-Polynomial.C b)).eval a=P.eval a-P.eval b := by
  have h:=congrArg (Polynomial.eval a) (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic P b)
  simpa only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    Polynomial.modByMonic_X_sub_C_eq_C_eval] using h

theorem reciprocalFactor_correct (P : Polynomial R) (a b : R)
    (ha : P.eval a=0) (hb : IsUnit (P.eval b)) :
    (a-b)*(reciprocalFactor P b).eval a=1 := by
  have h:=quotient_eval P a b
  rw [ha,zero_sub] at h
  simp only [reciprocalFactor,Polynomial.eval_mul,Polynomial.eval_C]
  calc
    _=Ring.inverse (P.eval b)*(-((a-b)*(P /ₘ (Polynomial.X-Polynomial.C b)).eval a)) := by ring
    _=1 := by rw [h,neg_neg,Ring.inverse_mul_cancel _ hb]

theorem groupPolynomial_root (group : I→C) (μ : I→R) (i : I) :
    (groupPolynomial group μ (group i)).eval (μ i)=0 := by
  simp only [groupPolynomial,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_eq_zero (show i∈members group (group i) by simp [members])
  simp

theorem groupPolynomial_unit (group : I→C) (μ : I→R)
    (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) (c : C) (j : I) (hj : group j≠c) :
    IsUnit ((groupPolynomial group μ c).eval (μ j)) := by
  simp only [groupPolynomial,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply IsUnit.prod_iff.mpr
  intro i hi
  have hg : group i=c := (Finset.mem_filter.mp hi).2
  exact hu j i (by rwa [hg])

theorem projector_eval (group : I→C) (μ : I→R)
    (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) (c : C) (i : I) :
    (projector group μ c).eval (μ i)=if group i=c then 1 else 0 := by
  by_cases hi:group i=c
  · rw [if_pos hi]
    simp only [projector,outsidePolynomial,Polynomial.eval_mul,Polynomial.eval_prod,
      Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,←Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j hj
    apply reciprocalFactor_correct
    · rw [←hi]
      exact groupPolynomial_root group μ i
    · exact groupPolynomial_unit group μ hu c j (Finset.mem_filter.mp hj).2
  · rw [if_neg hi]
    have hz : (outsidePolynomial group μ c).eval (μ i)=0 := by
      simp only [outsidePolynomial,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      apply Finset.prod_eq_zero (show i∈outsiders group c by simp [outsiders,hi])
      simp
    simp only [projector,Polynomial.eval_mul,hz,zero_mul]

def interpolant (group : I→C) (μ : I→R) (η : C→R) : Polynomial R:=
  ∑c,Polynomial.C (η c)*projector group μ c

theorem interpolant_eval (group : I→C) (μ : I→R) (η : C→R)
    (hu : ∀i j,group i≠group j→IsUnit (μ i-μ j)) (i : I) :
    (interpolant group μ η).eval (μ i)=η (group i) := by
  change (Polynomial.evalRingHom (μ i)) (∑c,Polynomial.C (η c)*projector group μ c)=_
  rw [map_sum]
  simp [projector_eval group μ hu,eq_comm]

section Degree
variable [Nontrivial R]

theorem groupPolynomial_degree (group : I→C) (μ : I→R) (c : C) :
    (groupPolynomial group μ c).natDegree≤(members group c).card := by
  simpa [groupPolynomial] using Polynomial.natDegree_prod_le (members group c)
    (fun i=>Polynomial.X-Polynomial.C (μ i))

theorem outsidePolynomial_degree (group : I→C) (μ : I→R) (c : C) :
    (outsidePolynomial group μ c).natDegree≤(outsiders group c).card := by
  simpa [outsidePolynomial] using Polynomial.natDegree_prod_le (outsiders group c)
    (fun i=>Polynomial.X-Polynomial.C (μ i))

theorem reciprocalFactor_degree (P : Polynomial R) (b : R) :
    (reciprocalFactor P b).natDegree≤P.natDegree := by
  apply le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C,zero_add,Polynomial.natDegree_divByMonic P (Polynomial.monic_X_sub_C b)]
  exact Nat.sub_le _ _

theorem projector_degree (group : I→C) (μ : I→R) (c : C) :
    (projector group μ c).natDegree≤Fintype.card I*(Fintype.card I+1) := by
  have hm : (members group c).card≤Fintype.card I:=Finset.card_le_univ _
  have ho : (outsiders group c).card≤Fintype.card I:=Finset.card_le_univ _
  have hp : (∏j∈outsiders group c,reciprocalFactor (groupPolynomial group μ c) (μ j)).natDegree≤
      (outsiders group c).card*(members group c).card := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      _≤∑j∈outsiders group c,(members group c).card := by
        apply Finset.sum_le_sum
        intro j _
        exact (reciprocalFactor_degree _ _).trans (groupPolynomial_degree group μ c)
      _=_ := by simp
  have hd := (Polynomial.natDegree_mul_le (p:=outsidePolynomial group μ c)
    (q:=∏j∈outsiders group c,reciprocalFactor (groupPolynomial group μ c) (μ j))).trans
      (Nat.add_le_add (outsidePolynomial_degree group μ c) hp)
  change (projector group μ c).natDegree≤_ at hd
  apply hd.trans
  calc
    _≤Fintype.card I+Fintype.card I*Fintype.card I :=
      Nat.add_le_add ho (Nat.mul_le_mul ho hm)
    _=_ := by ring

theorem interpolant_degree (group : I→C) (μ : I→R) (η : C→R) :
    (interpolant group μ η).natDegree≤Fintype.card I*(Fintype.card I+1) := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  apply (Polynomial.natDegree_mul_le).trans
  simpa only [Polynomial.natDegree_C,zero_add] using projector_degree group μ c

end Degree

end PlanarHom.GroupedProductInterpolation
