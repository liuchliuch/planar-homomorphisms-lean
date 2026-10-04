import PlanarHom.LinearFactorCoefficientMachines
import PlanarHom.RestrictedListFoldMachines
import PlanarHom.CoefficientListHeights

/-! # Actual product-coefficient compilation for fixed-alphabet interpolation nodes -/
namespace PlanarHom.LagrangeCoefficientMachines
open Turing Complexity ArithmeticCircuitPrimitives PairProjectionMachines MachineComposition
open LinearFactorCoefficientMachines
open scoped BigOperators
variable {K I : Type} [Field K]

def productCoefficients (nodes : List K) : List K := nodes.foldl (fun cs μ => mulLinear μ cs) [1]

theorem fold_length (cs nodes : List K) :
    (nodes.foldl (fun cs μ => mulLinear μ cs) cs).length=cs.length+nodes.length := by
  induction nodes generalizing cs with
  | nil => simp
  | cons μ nodes ih => simp [ih]; omega

@[simp] theorem productCoefficients_length (nodes : List K) : (productCoefficients nodes).length=nodes.length+1 := by
  simp [productCoefficients,fold_length,Nat.add_comm]

theorem fold_polynomial (cs nodes : List K) :
    coefficientPolynomial (nodes.foldl (fun cs μ => mulLinear μ cs) cs)=
      (nodes.map (fun μ => Polynomial.X-Polynomial.C μ)).prod*coefficientPolynomial cs := by
  induction nodes generalizing cs with
  | nil => simp
  | cons μ nodes ih =>
    simp only [List.foldl_cons,ih,coefficientPolynomial_mulLinear,List.map_cons,List.prod_cons]
    ring

theorem productCoefficients_polynomial (nodes : List K) :
    coefficientPolynomial (productCoefficients nodes)=(nodes.map (fun μ => Polynomial.X-Polynomial.C μ)).prod := by
  simp [productCoefficients,fold_polynomial,coefficientPolynomial]

theorem productCoefficients_ofFn (nodes : List K) :
    productCoefficients nodes=List.ofFn (fun i : Fin (nodes.length+1) =>
      ((nodes.map (fun μ => Polynomial.X-Polynomial.C μ)).prod).coeff i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have h := coefficientPolynomial_coeff (productCoefficients nodes) i
  rw [productCoefficients_polynomial,List.getElem?_eq_getElem hi,Option.getD_some] at h
  simpa only [List.getElem_ofFn] using h.symm

/-- Mathematical promise only: source words are not machine registers or inputs. -/
def NodesValid (A : I→K) (m : ℕ) (nodes : List K) : Prop :=
  ∀ μ∈nodes,∃word : List I,word.length=m ∧ (word.map A).prod=μ

variable [Algebra ℚ K] [Fintype I] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) (A : I→K)

/-- Exact coefficient-list height obtained from the already proved padded
fixed-alphabet expansion, with no algorithmic hypothesis. -/
theorem exists_product_length_bound : ∃p : Polynomial ℕ,∀m nodes,NodesValid A m nodes→
    ((numberFieldEncoding basis).list.encode (productCoefficients nodes)).length≤p.eval (nodes.length*(m+1)+1) := by
  classical
  obtain ⟨p,hp⟩ := CoefficientListHeights.exists_polynomial_coefficient_list_length_bound basis A
  refine ⟨p,?_⟩
  intro m nodes hnodes
  have hw : ∀i : Fin nodes.length,∃word : List I,word.length=m ∧ (word.map A).prod=nodes.get i :=
    fun i => hnodes _ (List.get_mem nodes i)
  choose words hlen hvalue using hw
  have h := hp nodes.length m words hlen
  have hpoly : (nodes.map (fun μ => Polynomial.X-Polynomial.C μ)).prod =
      ∏i : Fin nodes.length,(Polynomial.X-Polynomial.C ((words i).map A).prod) := by
    conv_lhs => rw [←List.ofFn_get nodes]
    simp only [List.map_ofFn,List.prod_ofFn,hvalue,Function.comp_apply]
  rw [productCoefficients_ofFn,hpoly]
  exact h

def Input := {p : ℕ×List K // NodesValid A p.1 p.2}

/-- The original unary m and materialized canonical node words are preserved. -/
noncomputable def inputEncoding : BitEncoding (Input A) :=
  (BitEncoding.unaryNat.prod (numberFieldEncoding basis).list).restrict (fun p => NodesValid A p.1 p.2)

noncomputable def foldStateEncoding : BitEncoding (ℕ×List K) :=
  BitEncoding.unaryNat.prod (numberFieldEncoding basis).list

/-- The coefficient seed [1] is physically inserted by actual pairing; the
promise only restricts values and never makes this preparation free. -/
noncomputable def preparedEncoding : BitEncoding (Input A) :=
  (((foldStateEncoding basis).prod (numberFieldEncoding basis).list).retract
    (fun p : ℕ×List K => ((p.1,[1]),p.2)) (fun p => (p.1.1,p.2)) (by intro p; rfl)).restrict
      (fun p => NodesValid A p.1 p.2)

def coefficientStep (s : ℕ×List K) (μ : K) : ℕ×List K := (s.1,mulLinear μ s.2)

omit [Algebra ℚ K] [Fintype I] in
theorem fold_coefficientStep (m : ℕ) (cs nodes : List K) :
    nodes.foldl coefficientStep (m,cs)=(m,nodes.foldl (fun cs μ => mulLinear μ cs) cs) := by
  induction nodes generalizing cs with
  | nil => rfl
  | cons μ nodes ih => simpa [coefficientStep] using ih (mulLinear μ cs)

theorem fp_coefficientStep : FP ((foldStateEncoding basis).prod (numberFieldEncoding basis))
    (foldStateEncoding basis) (fun p => coefficientStep p.1 p.2) := by
  have hs := fp_fst (foldStateEncoding basis) (numberFieldEncoding basis)
  have hm := hs.comp (fp_fst BitEncoding.unaryNat (numberFieldEncoding basis).list)
  have hcs := hs.comp (fp_snd BitEncoding.unaryNat (numberFieldEncoding basis).list)
  have hμ := fp_snd (foldStateEncoding basis) (numberFieldEncoding basis)
  exact hm.pair ((hμ.pair hcs).comp (fp_mulLinear basis))

omit [Fintype I] in
theorem fp_prepare : FP (inputEncoding basis A) (preparedEncoding basis A) id := by
  have hv : FP (inputEncoding basis A) (foldStateEncoding basis) (fun p => p.val) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hm := hv.comp (fp_fst BitEncoding.unaryNat (numberFieldEncoding basis).list)
  have hnodes := hv.comp (fp_snd BitEncoding.unaryNat (numberFieldEncoding basis).list)
  have hseed := fp_const (inputEncoding basis A) (numberFieldEncoding basis).list [1]
  exact ((hm.pair hseed).pair hnodes).transportOutput (fun _ => rfl)

/-- The complete product numerator list has an actual polynomial-time machine
on this honest fixed-alphabet source-product promise. -/
theorem fp_productCoefficients : FP (inputEncoding basis A) (numberFieldEncoding basis).list
    (fun p => productCoefficients p.val.2) := by
  obtain ⟨q,hq⟩ := exists_product_length_bound basis A
  obtain ⟨body⟩ := fp_coefficientStep basis
  let p : Polynomial ℕ := Polynomial.C 2*Polynomial.X+1+q.comp (Polynomial.X*(Polynomial.X+1)+1)
  have hsize (b : Input A) (i : ℕ) (hi : i≤b.val.2.length) :
      ((foldStateEncoding basis).encode ((b.val.2.take i).foldl coefficientStep (b.val.1,[1]))).length≤
        p.eval ((preparedEncoding basis A).encode b).length := by
    let N := ((preparedEncoding basis A).encode b).length
    have hN : N=2*(2*b.val.1+((numberFieldEncoding basis).list.encode [1]).length+1)+
        ((numberFieldEncoding basis).list.encode b.val.2).length+1 := by
      simp [N,preparedEncoding,BitEncoding.restrict,BitEncoding.retract,foldStateEncoding,
        BitEncoding.prod_length,BitEncoding.unaryNat_length]
    have hm : b.val.1≤N := by omega
    have hlen : b.val.2.length≤N :=
      (BitEncoding.list_length_le (numberFieldEncoding basis) b.val.2).trans (by omega)
    have ht : (b.val.2.take i).length≤N := by
      rw [List.length_take]
      exact (Nat.min_le_right _ _).trans hlen
    have hvalid : NodesValid A b.val.1 (b.val.2.take i) :=
      fun μ hμ => b.property μ (List.mem_of_mem_take hμ)
    have hbound := hq b.val.1 (b.val.2.take i) hvalid
    have harg : (b.val.2.take i).length*(b.val.1+1)+1≤N*(N+1)+1 := by nlinarith
    have hb := hbound.trans (natPolynomial_monotone q harg)
    dsimp only at hb
    rw [fold_coefficientStep]
    change ((foldStateEncoding basis).encode (b.val.1,productCoefficients (b.val.2.take i))).length≤_
    conv_lhs => simp only [foldStateEncoding,BitEncoding.prod_length,BitEncoding.unaryNat_length]
    simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change 2*b.val.1+((numberFieldEncoding basis).list.encode (productCoefficients (b.val.2.take i))).length+1≤
      2*N+1+q.eval (N*(N+1)+1)
    omega
  have loop := ListFoldMachines.computerOn (preparedEncoding basis A) (numberFieldEncoding basis)
    (foldStateEncoding basis) coefficientStep (fun b => (b.val.1,[1])) (fun b => b.val.2)
    (fun _ => rfl) body p hsize
  exact (((fp_prepare basis A).comp ⟨loop⟩).comp
    (fp_snd BitEncoding.unaryNat (numberFieldEncoding basis).list)).congr (fun b => by
      simp only [Function.comp_apply,id_eq,fold_coefficientStep,productCoefficients])

end PlanarHom.LagrangeCoefficientMachines
