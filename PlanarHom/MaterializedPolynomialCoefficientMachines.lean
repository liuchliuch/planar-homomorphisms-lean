import PlanarHom.MaterializedPolynomialInterpolationMachines
import PlanarHom.MaterializedCoefficientMachines
import PlanarHom.ListDropMachines

/-! NEW reconstruction: exact runtime coefficient extraction from a literal
Lagrange sample table. The degree index is binary and is never expanded into
an unbounded unary loop. All coefficient lists are bounded by table length. -/
namespace PlanarHom.MaterializedPolynomialCoefficientMachines
open Complexity PairProjectionMachines
open MaterializedPolynomialInterpolationMachines LagrangeCoefficientMachines
open LinearFactorCoefficientMachines
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K]

abbrev Input (K : Type) := ℕ × List (K × K)

def rowTerm (input : Input K) (row : K × K) : K :=
  let others := otherNodes row.1 input.2
  row.2 * (productCoefficients others).getD input.1 0 /
    differenceProduct (row.1,others)

def recover (input : Input K) : K := (input.2.map (rowTerm input)).sum

section Machines
variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def inputEncoding : BitEncoding (Input K) :=
  BitEncoding.nat.prod (MaterializedPolynomialInterpolationMachines.inputEncoding basis)

theorem fp_coefficientLookup : FP (BitEncoding.nat.prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (fun p => p.2.getD p.1 0) :=
  ((ListDropMachines.fp_drop (numberFieldEncoding basis) 0).comp
    (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)).congr (fun p => by
      simp [List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

theorem fp_rowTerm : FP ((inputEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
    (numberFieldEncoding basis) (fun p => rowTerm p.1 p.2) := by
  let e := numberFieldEncoding basis
  let tab := MaterializedPolynomialInterpolationMachines.inputEncoding basis
  have hi := fp_fst (inputEncoding basis) (e.prod e)
  have hd := hi.comp (fp_fst BitEncoding.nat tab)
  have ht := hi.comp (fp_snd BitEncoding.nat tab)
  have hr := fp_snd (inputEncoding basis) (e.prod e)
  have hx := hr.comp (fp_fst e e)
  have hy := hr.comp (fp_snd e e)
  have ho := (hx.pair ht).comp (fp_otherNodes basis)
  have hc := ho.comp (MaterializedCoefficientMachines.fp_productCoefficients basis)
  have hk := (hd.pair hc).comp (fp_coefficientLookup basis)
  have hn := (hx.pair ho).comp (fp_differenceProduct basis)
  exact (((hy.pair hk).comp (FixedFieldArithmetic.fp_multiplication basis)).pair hn).comp
    (FixedFieldArithmetic.fp_division basis)

/-- Total ordinary FP, including repeated nodes and arbitrarily large indices. -/
theorem fp_recover : FP (inputEncoding basis) (numberFieldEncoding basis)
    (recover : Input K → K) := by
  let e := numberFieldEncoding basis
  let tab := MaterializedPolynomialInterpolationMachines.inputEncoding basis
  have ht := fp_snd BitEncoding.nat tab
  have hm := ListContextMachines.fp_mapWithContext (inputEncoding basis) (e.prod e) e
    (fun p => rowTerm p.1 p.2) (fp_rowTerm basis)
  exact ((((fp_id (inputEncoding basis)).pair ht).comp hm).comp
    (MaterializedFieldListMachines.fp_sum basis))
end Machines

private theorem productCoefficients_getD (nodes : List K) (d : ℕ) :
    (productCoefficients nodes).getD d 0=
      ((nodes.map (fun μ => Polynomial.X-Polynomial.C μ)).prod).coeff d := by
  rw [← productCoefficients_polynomial,coefficientPolynomial_coeff]
  rfl

/-- The actual output is the requested coefficient of the Lagrange interpolant. -/
theorem recover_ofFn_eq_coeff_interpolate {n : ℕ} (d : ℕ) (nodes values : Fin n → K)
    (hnodes : Function.Injective nodes) :
    recover (d,List.ofFn (fun i => (nodes i,values i)))=
      (Lagrange.interpolate Finset.univ nodes values).coeff d := by
  unfold recover
  rw [List.map_ofFn,List.sum_ofFn,Lagrange.interpolate_apply,Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply,rowTerm,productCoefficients_getD,differenceProduct,otherNodes,
    List.map_ofFn,Function.comp_def]
  rw [filtered_product nodes hnodes j,filtered_product nodes hnodes j]
  simp only [Lagrange.basis,Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib,← map_prod,Finset.prod_inv_distrib,
    ← mul_assoc,← Polynomial.C_mul,Polynomial.coeff_C_mul]
  rw [div_eq_mul_inv]
  ring

/-- Exact samples recover any coefficient of the original polynomial, including
indices beyond its degree; only table distinctness and degree bound are needed. -/
theorem recover_ofFn_eq_coeff {n : ℕ} (d : ℕ) (nodes values : Fin n → K)
    (hnodes : Function.Injective nodes) (P : Polynomial K) (hdegree : P.degree<n)
    (hvalues : ∀ i,values i=P.eval (nodes i)) :
    recover (d,List.ofFn (fun i => (nodes i,values i)))=P.coeff d := by
  rw [recover_ofFn_eq_coeff_interpolate d nodes values hnodes]
  have hP : P=Lagrange.interpolate Finset.univ nodes values :=
    Lagrange.eq_interpolate_of_eval_eq values hnodes.injOn (by simpa using hdegree)
      (fun i _ => (hvalues i).symm)
  rw [← hP]

theorem recover_eq_coeff (d : ℕ) (table : List (K × K))
    (hnodes : (table.map Prod.fst).Nodup) (P : Polynomial K)
    (hdegree : P.degree<table.length) (hvalues : ∀ row∈table,row.2=P.eval row.1) :
    recover (d,table)=P.coeff d := by
  have h := recover_ofFn_eq_coeff d (fun i : Fin table.length => (table.get i).1)
    (fun i => (table.get i).2) (nodes_get_injective table hnodes) P hdegree
    (fun i => hvalues (table.get i) (List.get_mem table i))
  simpa only [Prod.eta,List.ofFn_get] using h
end PlanarHom.MaterializedPolynomialCoefficientMachines
