import PlanarHom.BooleanGroupedGridRecoverySemantics
import PlanarHom.BooleanGroupedTableRecoveryMachines

/-! Automatic degree and zero-constant bounds for the actual prepared table;
no degree or bit-height premise is required by the table recovery application. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanGroupedTableRecoverySemantics
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
open BooleanGroupedGridRecoveryMachines BooleanGroupedGridRecoverySemantics
open BooleanGroupedTableRecoveryMachines
variable {K : Type} [Field K] [Algebra ℚ K]

private theorem rootDegree {R : Type} [CommRing R] [Nontrivial R] (xs : List R) :
    (LinearProductDividedDifference.polynomial xs).natDegree ≤ xs.length := by
  induction xs with
  | nil => simp [LinearProductDividedDifference.polynomial]
  | cons a xs ih =>
    rw [LinearProductDividedDifference.polynomial_cons]
    apply Polynomial.natDegree_mul_le.trans
    have ha := Polynomial.natDegree_X_sub_C_le a
    simp only [List.length_cons]
    omega

theorem rowPolynomial_degree (n : ℕ) (ds : List K) (r : Row K n) :
    (rowPolynomial n ds r).natDegree ≤ r.2.2.length * (r.2.1.length+1) := by
  let R := Carrier (radicands ds) n
  let P := LinearProductDividedDifference.polynomial (R := R) r.2.1
  let qs := r.2.2.map (fun b : R => GroupedProductInterpolation.reciprocalFactor P b)
  have hs : (qs.map Polynomial.natDegree).sum ≤ r.2.2.length*r.2.1.length := by
    simp only [qs, List.map_map, Function.comp_def]
    apply ListMapMachines.sum_map_le_mul
    intro b _
    exact (GroupedProductInterpolation.reciprocalFactor_degree P b).trans (rootDegree (R := R) r.2.1)
  have hp := (Polynomial.natDegree_list_prod_le qs).trans hs
  have hout := rootDegree (R := R) r.2.2
  unfold rowPolynomial
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C, _root_.zero_add]
  apply Polynomial.natDegree_mul_le.trans
  change _ ≤ _ at hp
  nlinarith

theorem rowsPolynomial_degree (n : ℕ) (ds : List K) (rs : List (Row K n)) (d : ℕ)
    (h : ∀ r ∈ rs, (rowPolynomial n ds r).natDegree ≤ d) :
    (rowsPolynomial n ds rs).natDegree ≤ d := by
  induction rs with
  | nil => simp [rowsPolynomial]
  | cons r rs ih =>
    change (rowPolynomial n ds r + rowsPolynomial n ds rs).natDegree ≤ d
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (h r (by simp)) (ih (fun s hs => h s (by simp [hs]))))

def tablePolynomial (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n)) :
    Polynomial (Carrier (radicands ds) n) := rowsPolynomial n ds (rows n (ns,targets))

/-- The machine's chosen unary cap dominates its represented polynomial degree. -/
theorem tablePolynomial_degree (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n)) :
    (tablePolynomial n ds ns targets).natDegree ≤ degreeCap ns.length := by
  apply rowsPolynomial_degree
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  have hin : (selectNodes (n := n) true (q.2,ns)).length ≤ ns.length := by
    simp only [selectNodes, List.length_map]
    exact List.length_filter_le _ _
  have hout : (selectNodes (n := n) false (q.2,ns)).length ≤ ns.length := by
    simp only [selectNodes, List.length_map]
    exact List.length_filter_le _ _
  apply (rowPolynomial_degree n ds (makeRow n (ns,q))).trans
  simp only [makeRow, List.length_cons, degreeCap]
  nlinarith

/-- The actual recovery polynomial has zero constant coefficient because each
nonzero-target projector includes the inserted zero node as an outsider. -/
theorem tablePolynomial_zero (n : ℕ) (ds : List K) (ns : List (Node K n)) (targets : List (Tower K n)) :
    (tablePolynomial n ds ns targets).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold tablePolynomial rowsPolynomial
  change (Polynomial.evalRingHom (0 : Carrier (radicands ds) n)) _ = _
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hv
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hP
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  change (rowPolynomial n ds (makeRow n (ns,q))).eval 0 = 0
  simp only [rowPolynomial, makeRow, LinearProductDividedDifference.polynomial_cons,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [← zero_eq (radicands ds) n]
  simp

/-- Prepared-table recovery is its exact positive-moment coefficient functional;
the degree bound is discharged by the literal table lengths. -/
theorem recoverTower_eq_positive_functional (n : ℕ) (ds : List K)
    (ns : List (Node K n)) (targets : List (Tower K n))
    (y : Fin (degreeCap ns.length) → K)
    (hrows : ∀ r ∈ rows n (ns,targets), RowValid n ds r) :
    BooleanGroupedTableRecoveryMachines.recoverTower n (ds,(ns,(targets,List.ofFn y))) =
      ∑ r : Fin (degreeCap ns.length), (tablePolynomial n ds ns targets).coeff (r.val+1) *
        algebraMap K (Carrier (radicands ds) n) (y r) := by
  let y0 : Fin (degreeCap ns.length+1) → K := Fin.cases 0 y
  have hy0 : List.ofFn y0 = 0 :: List.ofFn y := by simp [y0, List.ofFn_succ]
  unfold BooleanGroupedTableRecoveryMachines.recoverTower prepare
  rw [← hy0, recoverTower_eq_coefficient_functional n ds (degreeCap ns.length)
    (rows n (ns,targets)) y0 hrows (tablePolynomial_degree n ds ns targets)]
  rw [Fin.sum_univ_succ]
  simp only [y0, Fin.cases_zero, _root_.map_zero, MulZeroClass.mul_zero, _root_.zero_add, Fin.cases_succ,
    Fin.val_succ, tablePolynomial]

end PlanarHom.BooleanGroupedTableRecoverySemantics
