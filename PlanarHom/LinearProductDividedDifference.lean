import PlanarHom.CoefficientListAlgebra

/-! Division-free evaluation of the quotient of a product of linear factors.
Repeated roots and zero divisors are allowed. -/
namespace PlanarHom.LinearProductDividedDifference
variable {R : Type} [CommRing R]

def term (z b : R) (nodes : List R) (j : ℕ) : R :=
  (nodes.zipIdx.map (fun p => if p.2 < j then b-p.1 else if j < p.2 then z-p.1 else 1)).prod

def value (z b : R) (nodes : List R) : R :=
  (nodes.zipIdx.map (fun p => term z b nodes p.2)).sum

@[simp] theorem term_cons_zero (z b a : R) (nodes : List R) :
    term z b (a::nodes) 0 = (nodes.map (fun x => z-x)).prod := by
  simp only [term, List.zipIdx_cons, List.map_cons, Nat.lt_irrefl, Nat.not_lt_zero,
    ↓reduceIte, List.prod_cons, List.zipIdx_succ, List.map_map, Function.comp_def,
    Nat.zero_lt_succ, one_mul]
  change ((nodes.zipIdx.map ((fun x : R => z-x) ∘ Prod.fst))).prod = _
  rw [← List.map_map, List.zipIdx_map_fst]

@[simp] theorem term_cons_succ (z b a : R) (nodes : List R) (j : ℕ) :
    term z b (a::nodes) (j+1) = (b-a) * term z b nodes j := by
  simp [term, List.zipIdx_cons, List.zipIdx_succ, List.map_map, Function.comp_def]

@[simp] theorem value_nil (z b : R) : value z b [] = 0 := rfl

@[simp] theorem value_cons (z b a : R) (nodes : List R) :
    value z b (a::nodes) = (nodes.map (fun x => z-x)).prod + (b-a)*value z b nodes := by
  simp only [value, List.zipIdx_cons, List.map_cons, List.sum_cons, term_cons_zero,
    List.zipIdx_succ, List.map_map, Function.comp_def, term_cons_succ]
  congr 1
  rw [List.sum_map_mul_left]

noncomputable def polynomial (nodes : List R) : Polynomial R :=
  (nodes.map (fun a => Polynomial.X - Polynomial.C a)).prod

noncomputable def quotient (b : R) : List R → Polynomial R
  | [] => 0
  | a::nodes => polynomial nodes + Polynomial.C (b-a) * quotient b nodes

@[simp] theorem polynomial_nil : polynomial ([] : List R) = 1 := rfl
@[simp] theorem polynomial_cons (a : R) (nodes : List R) :
    polynomial (a::nodes) = (Polynomial.X-Polynomial.C a)*polynomial nodes := rfl

@[simp] theorem polynomial_eval (z : R) (nodes : List R) :
    (polynomial nodes).eval z = (nodes.map (fun a => z-a)).prod := by
  simp [polynomial, Polynomial.eval_list_prod, List.map_map, Function.comp_def]

theorem quotient_eval (z b : R) (nodes : List R) :
    (quotient b nodes).eval z = value z b nodes := by
  induction nodes with
  | nil => simp [quotient]
  | cons a nodes ih => simp [quotient, ih]

theorem quotient_identity (b : R) (nodes : List R) :
    (Polynomial.X-Polynomial.C b)*quotient b nodes =
      polynomial nodes - Polynomial.C ((polynomial nodes).eval b) := by
  induction nodes with
  | nil => simp [quotient]
  | cons a nodes ih =>
    rw [quotient, polynomial_cons]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.C_mul, Polynomial.C_sub]
    calc
      _ = (Polynomial.X-Polynomial.C b)*polynomial nodes +
          (Polynomial.C b-Polynomial.C a)*((Polynomial.X-Polynomial.C b)*quotient b nodes) := by ring
      _ = _ := by rw [ih]; ring

theorem quotient_eq (b : R) (nodes : List R) :
    quotient b nodes = polynomial nodes /ₘ (Polynomial.X-Polynomial.C b) := by
  have h := Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic (polynomial nodes) b
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  have he := (quotient_identity b nodes).trans h.symm
  have hd := congrArg (fun p : Polynomial R => p /ₘ (Polynomial.X-Polynomial.C b)) he
  simpa only [Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C b)] using hd

/-- The executable double-map formula is the exact monic quotient evaluation. -/
theorem value_eq (z b : R) (nodes : List R) :
    value z b nodes = (polynomial nodes /ₘ (Polynomial.X-Polynomial.C b)).eval z := by
  rw [← quotient_eq, quotient_eval]

end PlanarHom.LinearProductDividedDifference
