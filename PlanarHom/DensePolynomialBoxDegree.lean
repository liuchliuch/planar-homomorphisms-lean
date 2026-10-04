import PlanarHom.DensePolynomialEvaluation

/-! NEW degree bounds in every fixed polynomial variable. Bounds concern the
original polynomial, and remain valid under arbitrary rational specialization. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial

def BoxDegree : (n:ℕ)→ℕ→Poly n→Prop
  | 0,_,_=>True
  | n+1,d,P=>P.natDegree≤d ∧ ∀k,BoxDegree n d (P.coeff k)

 theorem boxDegree_zero (n d:ℕ) : BoxDegree n d 0 := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨by simp,fun k=>by simpa using ih⟩

 theorem boxDegree_mono (n:ℕ) {d e:ℕ} {P:Poly n} (hd:d≤e) (h:BoxDegree n d P) :
    BoxDegree n e P := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨h.1.trans hd,fun k=>ih (h.2 k)⟩

 theorem boxDegree_add (n d:ℕ) {P Q:Poly n} (hP:BoxDegree n d P) (hQ:BoxDegree n d Q) :
    BoxDegree n d (P+Q) := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    refine ⟨(Polynomial.natDegree_add_le _ _).trans (max_le hP.1 hQ.1),?_⟩
    intro k
    rw [Polynomial.coeff_add]
    exact ih (hP.2 k) (hQ.2 k)

 theorem boxDegree_sum (n d:ℕ) {I:Type*} (s:Finset I) (P:I→Poly n)
    (h:∀i∈s,BoxDegree n d (P i)) : BoxDegree n d (∑i∈s,P i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using boxDegree_zero n d
  | @insert i s hi ih=>
    rw [Finset.sum_insert hi]
    exact boxDegree_add n d (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))

 theorem boxDegree_scalar (n d:ℕ) (q:ℚ) {P:Poly n} (h:BoxDegree n d P) :
    BoxDegree n d (qHom n q*P) := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    change (Polynomial.C (qHom n q)*(show Polynomial (Poly n) from P)).natDegree≤d ∧ _
    refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.1,?_⟩
    intro k
    change BoxDegree n d ((Polynomial.C (qHom n q)*(show Polynomial (Poly n) from P)).coeff k)
    rw [Polynomial.coeff_C_mul]
    exact ih (h.2 k)

 theorem boxDegree_one (n d:ℕ) : BoxDegree n d 1 := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    refine ⟨by simp,?_⟩
    intro k
    by_cases hk:k=0
    · subst k; simpa using ih
    · simpa [Polynomial.coeff_one,hk] using boxDegree_zero n d

 theorem boxDegree_qHom (n d:ℕ) (q:ℚ) : BoxDegree n d (qHom n q) := by
  simpa only [mul_one] using boxDegree_scalar n d q (boxDegree_one n d)

 theorem boxDegree_mul (n:ℕ) {d e:ℕ} {P Q:Poly n} (hP:BoxDegree n d P) (hQ:BoxDegree n e Q) :
    BoxDegree n (d+e) (P*Q) := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP.1 hQ.1),?_⟩
    intro k
    rw [Polynomial.coeff_mul]
    apply boxDegree_sum
    intro p hp
    exact ih (hP.2 p.1) (hQ.2 p.2)

 theorem boxDegree_eval (n d:ℕ) (P:Polynomial (Poly n)) (h:∀k,BoxDegree n d (P.coeff k)) (q:ℚ) :
    BoxDegree n d (P.eval (qHom n q)) := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  apply boxDegree_sum
  intro k hk
  rw [←map_pow,mul_comm]
  exact boxDegree_scalar n d (q^k) (h k)

end PlanarHom.DensePolynomial
