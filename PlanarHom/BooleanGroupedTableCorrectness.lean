import PlanarHom.BooleanGroupedTableRecoverySemantics
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Value correctness of the literal labeled-node recovery machine.  Repeated
nodes within a label are allowed, and the represented tower remains only a
commutative algebra.  All inverse promises follow from nonzero norms of nodes
and cross-label differences. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanGroupedTableCorrectness
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
open BooleanGroupedGridRecoveryMachines BooleanGroupedGridRecoverySemantics
open BooleanGroupedTableRecoveryMachines BooleanGroupedTableRecoverySemantics
variable {K : Type} [Field K]

/-- Multiplicativity of the recursive norm, without any independence hypothesis
on the radicands. -/
theorem norm_mul (D : ℕ → K) (n : ℕ) (p q : Carrier D n) :
    norm D n (p*q) = norm D n p * norm D n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a : Carrier D n := p.1
    let b : Carrier D n := p.2
    let c : Carrier D n := q.1
    let d : Carrier D n := q.2
    let r : Carrier D n := embed n (D n)
    have he : (a*c+r*(b*d))*(a*c+r*(b*d)) -
        r*((a*d+b*c)*(a*d+b*c)) =
        (a*a-r*(b*b))*(c*c-r*(d*d)) := by ring
    simp only [mul_eq, sub_eq, add_eq] at he
    simp only [mul_eq, norm, mul]
    rw [he]
    simpa only [mul_eq, sub_eq] using ih (a*a-r*(b*b)) (c*c-r*(d*d))

theorem norm_one (D : ℕ → K) (n : ℕ) :
    norm D n (1 : Carrier D n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let r : Carrier D n := embed n (D n)
    have he : (1 : Carrier D n)*1 - r*(0*0) = 1 := by ring
    simp only [mul_eq, sub_eq, one_eq, zero_eq, r] at he
    simpa only [one_eq, norm, embed, he] using ih

/-- The inverse norm promise is equivalent to being a unit in the represented
algebra, including when that algebra has zero divisors. -/
theorem norm_ne_zero_of_isUnit (D : ℕ → K) (n : ℕ) (p : Carrier D n)
    (hp : IsUnit p) : norm D n p ≠ 0 := by
  obtain ⟨u, rfl⟩ := hp
  have h := norm_mul D n (u : Carrier D n) u.inv
  rw [u.val_inv, norm_one] at h
  exact fun hz => (one_ne_zero : (1 : K) ≠ 0) (by simpa only [hz, MulZeroClass.zero_mul] using h)

theorem norm_ne_zero_iff_isUnit (D : ℕ → K) (n : ℕ) (p : Carrier D n) :
    norm D n p ≠ 0 ↔ IsUnit p :=
  ⟨BooleanFieldTowerInverse.isUnit_of_norm_ne_zero D n p,
    norm_ne_zero_of_isUnit D n p⟩

section Lists
variable {R : Type} [CommRing R]

private theorem polynomial_root (xs : List R) (a : R) (ha : a ∈ xs) :
    (LinearProductDividedDifference.polynomial xs).eval a = 0 := by
  rw [LinearProductDividedDifference.polynomial_eval]
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨a, ha, sub_self a⟩

private theorem polynomial_unit (xs : List R) (b : R)
    (h : ∀ a ∈ xs, IsUnit (b-a)) :
    IsUnit ((LinearProductDividedDifference.polynomial xs).eval b) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [LinearProductDividedDifference.polynomial_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact (h a (by simp)).mul (ih (fun x hx => h x (by simp [hx])))

private theorem list_projector_inside (inside outside : List R) (a : R)
    (ha : a ∈ inside)
    (hu : ∀ b ∈ outside,
      IsUnit ((LinearProductDividedDifference.polynomial inside).eval b)) :
    (LinearProductDividedDifference.polynomial outside *
      (outside.map (GroupedProductInterpolation.reciprocalFactor
        (LinearProductDividedDifference.polynomial inside))).prod).eval a = 1 := by
  simp only [Polynomial.eval_mul, LinearProductDividedDifference.polynomial_eval,
    Polynomial.eval_list_prod, List.map_map, Function.comp_def]
  rw [← List.prod_map_mul]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact GroupedProductInterpolation.reciprocalFactor_correct _ a b
    (polynomial_root inside a ha) (hu b hb)

private theorem list_projector_outside (inside outside : List R) (a : R)
    (ha : a ∈ outside) :
    (LinearProductDividedDifference.polynomial outside *
      (outside.map (GroupedProductInterpolation.reciprocalFactor
        (LinearProductDividedDifference.polynomial inside))).prod).eval a = 0 := by
  rw [Polynomial.eval_mul, polynomial_root outside a ha, MulZeroClass.zero_mul]

end Lists

variable [Algebra ℚ K]

omit [Field K] [Algebra ℚ K] in
theorem mem_selectNodes_same (n : ℕ) (ns : List (Node K n)) (c : ℕ) (a : Tower K n) :
    a ∈ selectNodes true (c,ns) ↔ ∃ q ∈ ns, q.1 = c ∧ q.2 = a := by
  simp [selectNodes, and_assoc]

omit [Field K] [Algebra ℚ K] in
theorem mem_selectNodes_other (n : ℕ) (ns : List (Node K n)) (c : ℕ) (a : Tower K n) :
    a ∈ selectNodes false (c,ns) ↔ ∃ q ∈ ns, q.1 ≠ c ∧ q.2 = a := by
  simp [selectNodes, and_assoc]

omit [Algebra ℚ K] in
/-- Every denominator of the actual row program has nonzero norm. -/
theorem makeRow_valid (n : ℕ) (ds : List K) (ns : List (Node K n))
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (target : Tower K n) (c : ℕ) : RowValid n ds (makeRow n (ns,(target,c))) := by
  intro b hb
  apply norm_ne_zero_of_isUnit
  apply polynomial_unit
  intro a ha
  obtain ⟨q, hq, hqc, rfl⟩ := (mem_selectNodes_same n ns c a).mp ha
  rcases List.mem_cons.mp hb with hb | hb
  · subst b
    have hq' := BooleanFieldTowerInverse.isUnit_of_norm_ne_zero (radicands ds) n q.2 (hnode q hq)
    simpa only [← zero_eq (radicands ds) n, zero_sub] using hq'.neg
  · obtain ⟨r, hr, hrc, rfl⟩ := (mem_selectNodes_other n ns c b).mp hb
    simpa only [sub_eq] using BooleanFieldTowerInverse.isUnit_of_norm_ne_zero (radicands ds) n
      (sub n r.2 q.2) (hcross r hr q hq (by simpa only [hqc] using hrc))

omit [Algebra ℚ K] in
/-- The executable row is the target on its own label and zero on every other
label; no distinctness is imposed on equal-label values. -/
theorem makeRow_eval (n : ℕ) (ds : List K) (ns : List (Node K n))
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (target : Tower K n) (c : ℕ) (q : Node K n) (hq : q ∈ ns) :
    (rowPolynomial n ds (makeRow n (ns,(target,c)))).eval (ofTower (radicands ds) n q.2) =
      if q.1 = c then ofTower (radicands ds) n target else 0 := by
  have hv := makeRow_valid n ds ns hnode hcross target c
  unfold rowPolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hc : q.1 = c
  · rw [if_pos hc, list_projector_inside, mul_one]
    · rfl
    · exact (mem_selectNodes_same n ns c q.2).mpr ⟨q,hq,hc,rfl⟩
    · intro b hb
      exact BooleanFieldTowerInverse.isUnit_of_norm_ne_zero (radicands ds) n _ (hv b hb)
  · rw [if_neg hc, list_projector_outside, MulZeroClass.mul_zero]
    exact List.mem_cons_of_mem _ ((mem_selectNodes_other n ns c q.2).mpr ⟨q,hq,hc,rfl⟩)

omit [Algebra ℚ K] in
/-- Every row in the literal prepared table satisfies the runtime inverse
promise. This also covers empty tables and labels with no nodes. -/
theorem rows_valid (n : ℕ) (ds : List K) (ns : List (Node K n))
    (targets : List (Tower K n))
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0) :
    ∀ r ∈ rows n (ns,targets), RowValid n ds r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact makeRow_valid n ds ns hnode hcross q.1 q.2

omit [Algebra ℚ K] in
private theorem rows_eq_ofFn (n : ℕ) (ns : List (Node K n))
    (targets : List (Tower K n)) :
    rows n (ns,targets) = List.ofFn (fun i : Fin targets.length =>
      makeRow n (ns,(targets[i.val],i.val))) := by
  apply List.ext_getElem
  · simp [rows]
  · intro i hi hi'
    simp [rows]

/-- Interpolation at each actual stored node, indexed by its literal label. -/
theorem tablePolynomial_eval (n : ℕ) (ds : List K) (ns : List (Node K n))
    (targets : List (Tower K n))
    (hlabel : ∀ q ∈ ns, q.1 < targets.length)
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (q : Node K n) (hq : q ∈ ns) :
    (tablePolynomial n ds ns targets).eval (ofTower (radicands ds) n q.2) =
      ofTower (radicands ds) n (targets[q.1]'(hlabel q hq)) := by
  unfold tablePolynomial rowsPolynomial
  rw [rows_eq_ofFn, List.map_ofFn, List.sum_ofFn, Polynomial.eval_finset_sum]
  simp only [Function.comp_def]
  simp_rw [makeRow_eval n ds ns hnode hcross _ _ q hq]
  let j : Fin targets.length := ⟨q.1,hlabel q hq⟩
  rw [Finset.sum_eq_single j]
  · simp [j]
  · intro k hk hkj
    exact if_neg (fun h => hkj (Fin.ext h.symm))
  · simp

/-- The exact positive-moment functional of the machine recovers arbitrary
signed tower weights against the actual node labels. -/
theorem recoverTower_eq_weighted_targets_ofFn {A : Type} [Fintype A]
    (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n))
    (hlabel : ∀ q ∈ ns, q.1 < targets.length)
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (node : A → Fin ns.length) (weight : A → Carrier (radicands ds) n)
    (y : Fin (degreeCap ns.length) → K)
    (hy : ∀ h, algebraMap K (Carrier (radicands ds) n) (y h) =
      ∑ a, weight a * (ofTower (radicands ds) n (ns[(node a).val].2))^(h.val+1)) :
    BooleanGroupedTableRecoveryMachines.recoverTower n (ds,(ns,(targets,List.ofFn y))) =
      ∑ a, weight a * ofTower (radicands ds) n
        (targets[(ns[(node a).val]).1]'(hlabel _ (List.getElem_mem _))) := by
  rw [recoverTower_eq_positive_functional n ds ns targets y
    (rows_valid n ds ns targets hnode hcross)]
  let P := tablePolynomial n ds ns targets
  have heval (a : A) :
      (∑ h : Fin (degreeCap ns.length), P.coeff (h.val+1) *
        (ofTower (radicands ds) n (ns[(node a).val].2))^(h.val+1)) =
      ofTower (radicands ds) n
        (targets[(ns[(node a).val]).1]'(hlabel _ (List.getElem_mem _))) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun h => P.coeff (h+1) * (ofTower (radicands ds) n (ns[(node a).val].2))^(h+1))]
    have h := Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (tablePolynomial_degree n ds ns targets))
      (ofTower (radicands ds) n (ns[(node a).val].2))
    rw [Finset.sum_range_succ'] at h
    simp only [tablePolynomial_zero, MulZeroClass.zero_mul, _root_.add_zero] at h
    exact h.symm.trans (tablePolynomial_eval n ds ns targets hlabel hnode hcross
      _ (List.getElem_mem _))
  simp_rw [hy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (M := Carrier (radicands ds) n) rfl
  intro a _
  change (∑ h : Fin (degreeCap ns.length), P.coeff (h.val+1) *
    (weight a * (ofTower (radicands ds) n (ns[(node a).val].2))^(h.val+1))) = _
  rw [← heval a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Literal list-input correctness. The only oracle premise is the equality of
its embedded positive moments with the actual weighted powers, for exactly the
computed cap many answers. -/
theorem recoverTower_eq_weighted_targets {A : Type} [Fintype A]
    (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n))
    (hlabel : ∀ q ∈ ns, q.1 < targets.length)
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (node : A → Fin ns.length) (weight : A → Carrier (radicands ds) n)
    (positiveMoments : List K) (hlength : positiveMoments.length = degreeCap ns.length)
    (hmoment : ∀ h : Fin (degreeCap ns.length),
      algebraMap K (Carrier (radicands ds) n)
        (positiveMoments[h.val]'(by rw [hlength]; exact h.isLt)) =
      ∑ a, weight a * (ofTower (radicands ds) n (ns[(node a).val].2))^(h.val+1)) :
    BooleanGroupedTableRecoveryMachines.recoverTower n (ds,(ns,(targets,positiveMoments))) =
      ∑ a, weight a * ofTower (radicands ds) n
        (targets[(ns[(node a).val]).1]'(hlabel _ (List.getElem_mem _))) := by
  let y : Fin (degreeCap ns.length) → K := fun h =>
    positiveMoments[h.val]'(by rw [hlength]; exact h.isLt)
  have hy : List.ofFn y = positiveMoments := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlength]
    · intro i hi hi'
      simp only [List.getElem_ofFn, y]
  rw [← hy]
  exact recoverTower_eq_weighted_targets_ofFn n ds ns targets hlabel hnode hcross
    node weight y hmoment

/-- Actual base-coordinate extraction recovers a base-field target once the
weighted target contraction is represented by its base embedding. -/
theorem recover_eq_of_weighted_targets_embed {A : Type} [Fintype A]
    (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n))
    (hlabel : ∀ q ∈ ns, q.1 < targets.length)
    (hnode : ∀ q ∈ ns, norm (radicands ds) n q.2 ≠ 0)
    (hcross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
      norm (radicands ds) n (sub n q.2 r.2) ≠ 0)
    (node : A → Fin ns.length) (weight : A → Carrier (radicands ds) n)
    (positiveMoments : List K) (hlength : positiveMoments.length = degreeCap ns.length)
    (hmoment : ∀ h : Fin (degreeCap ns.length),
      algebraMap K (Carrier (radicands ds) n)
        (positiveMoments[h.val]'(by rw [hlength]; exact h.isLt)) =
      ∑ a, weight a * (ofTower (radicands ds) n (ns[(node a).val].2))^(h.val+1))
    (value : K)
    (hvalue : (∑ a, weight a * ofTower (radicands ds) n
      (targets[(ns[(node a).val]).1]'(hlabel _ (List.getElem_mem _)))) = embed n value) :
    BooleanGroupedTableRecoveryMachines.recover n (ds,(ns,(targets,positiveMoments))) = value := by
  change BooleanFieldTowerInverse.constantCoeff n
    (BooleanGroupedTableRecoveryMachines.recoverTower n (ds,(ns,(targets,positiveMoments)))) = value
  rw [recoverTower_eq_weighted_targets n ds ns targets hlabel hnode hcross
    node weight positiveMoments hlength hmoment, hvalue,
    BooleanFieldTowerInverse.constantCoeff_embed]

end PlanarHom.BooleanGroupedTableCorrectness
