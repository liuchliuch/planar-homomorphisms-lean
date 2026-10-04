import PlanarHom.LinearFoldMachines
import PlanarHom.BooleanFieldTowerLinearization
import PlanarHom.DependentMonomialMachines

/-! Actual variable-length products in a fixed radical algebra, with all
radicands materialized in the input. Shared coordinate denominators establish
polynomial bounds for every prefix, without assuming the algebra is a field. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanFieldTowerProductMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerLinearization
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def radicands (xs : List K) (i : ℕ) : K := xs[i]?.getD 0

def inputEncoding (n : ℕ) : BitEncoding (List K × (Tower K n × List (Tower K n))) :=
  (numberFieldEncoding basis).list.prod ((encoding basis n).prod (encoding basis n).list)

def product (n : ℕ) (p : List K × (Tower K n × List (Tower K n))) : Tower K n :=
  p.2.2.foldl (mul (radicands p.1) n) p.2.1

instance indexNonempty (n : ℕ) : Nonempty (Index n) :=
  Fintype.card_pos_iff.mp (by rw [index_card]; positivity)

theorem fp_radicands (i : ℕ) :
    FP (numberFieldEncoding basis).list (numberFieldEncoding basis) (fun xs => radicands xs i) :=
  DependentMonomialMachines.fp_getD (numberFieldEncoding basis) 0 i

theorem fp_entry (n : ℕ) (i : Index n × Index n) :
    FP ((numberFieldEncoding basis).list.prod (encoding basis n)) (numberFieldEncoding basis)
      (fun p => multiplicationMatrix (radicands p.1) n p.2 i.1 i.2) := by
  apply fp_multiplicationMatrix
  · intro k
    exact (fp_fst _ _).comp (fp_radicands basis k)
  · exact fp_snd _ _

theorem fp_step (n : ℕ) :
    FP (((numberFieldEncoding basis).list.prod (encoding basis n)).prod (encoding basis n))
      ((numberFieldEncoding basis).list.prod (encoding basis n))
      (fun p => LinearFoldMachines.step (fun ds => mul (radicands ds) n) p.1 p.2) := by
  let ec := (numberFieldEncoding basis).list
  let ev := encoding basis n
  let e := (ec.prod ev).prod ev
  have hs := fp_fst (ec.prod ev) ev
  have hc := hs.comp (fp_fst ec ev)
  have hv := hs.comp (fp_snd ec ev)
  have ha := fp_snd (ec.prod ev) ev
  exact hc.pair (fp_mul basis e (fun p => radicands p.1.1)
    (fun i => hc.comp (fp_radicands basis i)) n _ _ hv ha)

theorem exists_state_prefix_size_bound (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (v : List K × Tower K n) (xs : List (Tower K n)) (i : ℕ),
      (((numberFieldEncoding basis).list.prod (encoding basis n)).encode
        ((xs.take i).foldl (LinearFoldMachines.step (fun ds => mul (radicands ds) n)) v)).length ≤
      p.eval (((((numberFieldEncoding basis).list.prod (encoding basis n)).prod
        (encoding basis n).list)).encode (v,xs)).length := by
  apply LinearFoldMachines.exists_prefix_size_bound basis (M:=4^n)
    (numberFieldEncoding basis).list (encoding basis n) (encoding basis n)
    (fun ds => mul (radicands ds) n) (coord n)
    (fun ds q ij => multiplicationMatrix (radicands ds) n q ij.1 ij.2)
  · exact fun ds p q i => coord_mul_matrix (radicands ds) n p q i
  · exact coord_length_le basis n
  · intro p L h
    exact (Nat.le_add_right _ 1).trans (encoding_length_le basis n p L h)
  · exact fp_entry basis n

/-- The input serialization bounds every actual product accumulator prefix. -/
theorem exists_polynomial_prefix_encoding_bound (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (ds : List K) (a : Tower K n) (xs : List (Tower K n)) (i : ℕ),
      ((encoding basis n).encode ((xs.take i).foldl (mul (radicands ds) n) a)).length ≤
        p.eval ((inputEncoding basis n).encode (ds,(a,xs))).length := by
  obtain ⟨p,hp⟩ := exists_state_prefix_size_bound basis n
  refine ⟨p.comp (Polynomial.C 2*Polynomial.X+Polynomial.C 1),fun ds a xs i => ?_⟩
  have h := hp (ds,a) xs i
  rw [LinearFoldMachines.fold_step,BitEncoding.prod_length] at h
  dsimp only at h
  have hs : ((encoding basis n).encode ((xs.take i).foldl (mul (radicands ds) n) a)).length ≤
      p.eval (((((numberFieldEncoding basis).list.prod (encoding basis n)).prod
        (encoding basis n).list)).encode ((ds,a),xs)).length := by omega
  apply hs.trans
  simp only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  apply MachineComposition.natPolynomial_monotone
  simp only [inputEncoding,BitEncoding.prod_length]
  omega

/-- A genuine polynomial-time left-fold computer over arbitrary materialized
factors and radicands. No size-growth premise and no field instance on Tower. -/
theorem fp_product (n : ℕ) :
    FP (inputEncoding basis n) (encoding basis n) (product n) := by
  apply LinearFoldMachines.fp_fold basis (M:=4^n)
    (numberFieldEncoding basis).list (encoding basis n) (encoding basis n)
    (fun ds => mul (radicands ds) n) (coord n)
    (fun ds q ij => multiplicationMatrix (radicands ds) n q ij.1 ij.2)
  · exact fun ds p q i => coord_mul_matrix (radicands ds) n p q i
  · exact coord_length_le basis n
  · intro p L h
    exact (Nat.le_add_right _ 1).trans (encoding_length_le basis n p L h)
  · exact fp_entry basis n
  · exact fp_step basis n

open BooleanFieldTowerAlgebra

/-- The concrete accumulator fold is the ordinary product in the represented
commutative algebra, including square, repeated, and zero radicands. -/
theorem fold_mul_eq (D : ℕ → K) (n : ℕ) (xs : List (Carrier D n)) (a : Carrier D n) :
    xs.foldl (mul D n) a = a * xs.prod := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil,List.prod_nil,mul_one]
  | cons b xs ih =>
    simp only [List.foldl_cons,List.prod_cons,ih]
    rw [← mul_eq D n a b]
    exact mul_assoc a b xs.prod

theorem product_eq (n : ℕ) (ds : List K)
    (a : Carrier (radicands ds) n) (xs : List (Carrier (radicands ds) n)) :
    product n (ds,(a,xs)) = a * xs.prod :=
  fold_mul_eq (radicands ds) n xs a

end PlanarHom.BooleanFieldTowerProductMachines
