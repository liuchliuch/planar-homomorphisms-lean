import PlanarHom.MaterializedFieldListMachines
import PlanarHom.ListContextFilterMachines
import Mathlib.LinearAlgebra.Lagrange

/-! # Actual polynomial interpolation from materialized node/value pairs

The input is a literal list of pairs in one fixed number-field encoding.  The
total program evaluates the ordinary, unshifted Lagrange formula at a fixed
point.  Distinctness and the polynomial degree bound belong only to correctness,
not to the polynomial-time machine.  Zero nodes, zero values, signed values,
and evaluation at one of the nodes require no extra promise.
-/

namespace PlanarHom.MaterializedPolynomialInterpolationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open scoped BigOperators

variable {K : Type} [Field K] [DecidableEq K]

/-- Delete by node value, preserving the materialized list order. -/
def otherNodes (node : K) (table : List (K × K)) : List K :=
  (table.map Prod.fst).filter (fun x => decide (x ≠ node))

/-- The empty product is one; this is the ordinary unshifted numerator/denominator. -/
def differenceProduct (p : K × List K) : K :=
  (p.2.map (fun x => p.1 - x)).prod

/-- A total Lagrange row. Division uses the field's total inverse, even on invalid tables. -/
def rowTerm (x₀ : K) (table : List (K × K)) (row : K × K) : K :=
  row.2 * differenceProduct (x₀, otherNodes row.1 table) /
    differenceProduct (row.1, otherNodes row.1 table)

/-- Evaluate the literal ordinary Lagrange sum; the empty input returns zero. -/
def recover (x₀ : K) (table : List (K × K)) : K :=
  (table.map (rowTerm x₀ table)).sum

@[simp] theorem recover_nil (x₀ : K) : recover x₀ [] = 0 := rfl

@[simp] theorem recover_singleton (x₀ x y : K) : recover x₀ [(x, y)] = y := by
  simp [recover, rowTerm, differenceProduct, otherNodes]

section Machines
variable [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The original field codec, paired and framed as a list, with no validity restriction. -/
noncomputable def inputEncoding : BitEncoding (List (K × K)) :=
  ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list

theorem fp_otherNodes : FP ((numberFieldEncoding basis).prod (inputEncoding basis))
    (numberFieldEncoding basis).list (fun p => otherNodes p.1 p.2) := by
  let e := numberFieldEncoding basis
  have hx := fp_fst e (inputEncoding basis)
  have ht := fp_snd e (inputEncoding basis)
  have hn := ht.comp (ListMapMachines.fp_map (e.prod e) e Prod.fst (fp_fst e e))
  have hneq : FP (e.prod e) BitEncoding.bool (fun p : K × K => decide (p.2 ≠ p.1)) :=
    ((FixedFieldArithmetic.fp_equality basis).comp (fp_bool_unary BitEncoding.bool not)).congr
      (fun p => by simp [eq_comm])
  exact (hx.pair hn).comp (ListContextFilterMachines.fp_filterWithContext e e _ hneq)

omit [DecidableEq K] in
theorem fp_differenceProduct : FP ((numberFieldEncoding basis).prod
    (numberFieldEncoding basis).list) (numberFieldEncoding basis) differenceProduct := by
  have hd := ListContextMachines.fp_mapWithContext (numberFieldEncoding basis)
    (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun p : K × K => p.1 - p.2) (FixedFieldArithmetic.fp_subtraction basis)
  exact hd.comp (MaterializedFieldListMachines.fp_product basis)

/-- Each row is compiled from actual filtering, subtraction, products, multiplication,
and total division. Materialized input bounds discharge all intermediate growth. -/
theorem fp_rowTerm (x₀ : K) : FP ((inputEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
    (numberFieldEncoding basis) (fun p => rowTerm x₀ p.1 p.2) := by
  let e := numberFieldEncoding basis
  have ht := fp_fst (inputEncoding basis) (e.prod e)
  have hr := fp_snd (inputEncoding basis) (e.prod e)
  have hx := hr.comp (fp_fst e e)
  have hy := hr.comp (fp_snd e e)
  have ho := (hx.pair ht).comp (fp_otherNodes basis)
  have hx₀ := fp_const ((inputEncoding basis).prod (e.prod e)) e x₀
  have hn := (hx₀.pair ho).comp (fp_differenceProduct basis)
  have hd := (hx.pair ho).comp (fp_differenceProduct basis)
  have hmul := (hy.pair hn).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact (hmul.pair hd).comp (FixedFieldArithmetic.fp_division basis)

/-- Ordinary total FP from the materialized table to the original number-field codec.
There is no degree, sign, distinctness, nonzero-node, or output-growth hypothesis. -/
theorem fp_recover (x₀ : K) :
    FP (inputEncoding basis) (numberFieldEncoding basis) (recover x₀) := by
  have hm := ListContextMachines.fp_mapWithContext (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) (numberFieldEncoding basis)
    (fun p => rowTerm x₀ p.1 p.2) (fp_rowTerm basis x₀)
  exact ((((fp_id (inputEncoding basis)).pair (fp_id (inputEncoding basis))).comp hm).comp
    (MaterializedFieldListMachines.fp_sum basis))

end Machines

omit [Field K] in
/-- Under node distinctness, value filtering is precisely positional exclusion. -/
theorem filtered_product {n : ℕ} {S : Type} [CommMonoid S]
    (nodes : Fin n → K) (hnodes : Function.Injective nodes) (j : Fin n) (f : K → S) :
    (((List.ofFn nodes).filter (fun x => decide (x ≠ nodes j))).map f).prod =
      ∏ i ∈ Finset.univ.erase j, f (nodes i) := by
  have hp := List.prod_map_ite (fun x => x ≠ nodes j) f (fun _ => (1 : S)) (List.ofFn nodes)
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at hp
  rw [← hp, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ne_eq, hnodes.eq_iff]
  rw [← Finset.prod_filter, Finset.filter_ne']

/-- This identifies the compiled function itself with the evaluated Lagrange polynomial.
It imposes no restriction on the evaluation point or on the sample values. -/
theorem recover_ofFn_eq_eval_interpolate {n : ℕ} (x₀ : K) (nodes values : Fin n → K)
    (hnodes : Function.Injective nodes) :
    recover x₀ (List.ofFn (fun i => (nodes i, values i))) =
      (Lagrange.interpolate Finset.univ nodes values).eval x₀ := by
  unfold recover
  rw [List.map_ofFn, List.sum_ofFn, Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, rowTerm, differenceProduct, otherNodes,
    List.map_ofFn, Function.comp_def]
  rw [filtered_product nodes hnodes j, filtered_product nodes hnodes j]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis, Polynomial.eval_prod,
    Lagrange.basisDivisor, Polynomial.eval_sub, Polynomial.eval_X]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  simp only [div_eq_mul_inv]
  ring

/-- Arbitrary exact samples recover every polynomial of degree less than the node count.
The `degree` formulation includes the empty table and its unique admissible polynomial, zero. -/
theorem recover_ofFn_eq_eval {n : ℕ} (x₀ : K) (nodes values : Fin n → K)
    (hnodes : Function.Injective nodes) (P : Polynomial K) (hdegree : P.degree < n)
    (hvalues : ∀ i, values i = P.eval (nodes i)) :
    recover x₀ (List.ofFn (fun i => (nodes i, values i))) = P.eval x₀ := by
  rw [recover_ofFn_eq_eval_interpolate x₀ nodes values hnodes]
  have hP : P = Lagrange.interpolate Finset.univ nodes values :=
    Lagrange.eq_interpolate_of_eval_eq values hnodes.injOn (by simpa using hdegree)
      (fun i _ => (hvalues i).symm)
  rw [← hP]

/-- At a node the same program returns that node's sample; no separate branch is needed. -/
theorem recover_ofFn_at_node {n : ℕ} (nodes values : Fin n → K)
    (hnodes : Function.Injective nodes) (j : Fin n) :
    recover (nodes j) (List.ofFn (fun i => (nodes i, values i))) = values j := by
  rw [recover_ofFn_eq_eval_interpolate (nodes j) nodes values hnodes]
  exact Lagrange.eval_interpolate_at_node values hnodes.injOn (Finset.mem_univ j)

omit [Field K] [DecidableEq K] in
/-- Distinct materialized node words induce an injective positional node map. -/
theorem nodes_get_injective (table : List (K × K)) (hnodes : (table.map Prod.fst).Nodup) :
    Function.Injective (fun i : Fin table.length => (table.get i).1) := by
  apply List.nodup_ofFn.mp
  change (List.ofFn (Prod.fst ∘ table.get)).Nodup
  rw [← List.map_ofFn]
  simpa only [List.ofFn_get] using hnodes

/-- Correctness directly on the materialized input list used by `fp_recover`. -/
theorem recover_eq_eval (x₀ : K) (table : List (K × K))
    (hnodes : (table.map Prod.fst).Nodup) (P : Polynomial K)
    (hdegree : P.degree < table.length)
    (hvalues : ∀ row ∈ table, row.2 = P.eval row.1) :
    recover x₀ table = P.eval x₀ := by
  have h := recover_ofFn_eq_eval x₀ (fun i : Fin table.length => (table.get i).1)
    (fun i => (table.get i).2) (nodes_get_injective table hnodes) P hdegree
    (fun i => hvalues (table.get i) (List.get_mem table i))
  simpa only [Prod.eta, List.ofFn_get] using h

/-- Evaluating at any listed node returns its associated value, also for node zero. -/
theorem recover_at_node (table : List (K × K)) (hnodes : (table.map Prod.fst).Nodup)
    (j : Fin table.length) :
    recover (table.get j).1 table = (table.get j).2 := by
  have h := recover_ofFn_at_node (fun i : Fin table.length => (table.get i).1)
    (fun i => (table.get i).2) (nodes_get_injective table hnodes) j
  simpa only [Prod.eta, List.ofFn_get] using h

/-- The membership form of exact evaluation at a node. -/
theorem recover_at_mem (table : List (K × K)) (hnodes : (table.map Prod.fst).Nodup)
    (x y : K) (hrow : (x, y) ∈ table) : recover x table = y := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hrow
  simpa only [hj] using recover_at_node table hnodes j

/-- A convenient actual-sample-list interface, without separately supplied value equations. -/
theorem recover_samples (x₀ : K) (nodes : List K) (hnodes : nodes.Nodup)
    (P : Polynomial K) (hdegree : P.degree < nodes.length) :
    recover x₀ (nodes.map (fun x => (x, P.eval x))) = P.eval x₀ := by
  apply recover_eq_eval x₀ _ (by simpa [Function.comp_def] using hnodes) P (by simpa using hdegree)
  intro row hrow
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
  rfl

end PlanarHom.MaterializedPolynomialInterpolationMachines
