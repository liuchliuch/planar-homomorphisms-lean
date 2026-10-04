import PlanarHom.CoefficientListAlgebra

/-! Runtime coefficient convolution over a commutative ring. -/
namespace PlanarHom.CoefficientListAlgebra
variable {R : Type} [CommRing R]

theorem polynomial_coeff (cs : List R) (i : ℕ) :
    (polynomial cs).coeff i = cs[i]?.getD 0 := by
  induction cs generalizing i with
  | nil => simp [polynomial]
  | cons c cs ih => cases i <;> simp [polynomial, Polynomial.coeff_add, ih]

theorem polynomial_natDegree_le (cs : List R) : (polynomial cs).natDegree ≤ cs.length := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [polynomial_coeff, List.getElem?_eq_none (by omega)]
  rfl

def convolutionCoefficient (xs ys : List R) (k : ℕ) : R :=
  (xs.zipIdx.map (fun p => if k < p.2 then 0 else p.1 * ys[k-p.2]?.getD 0)).sum

@[simp] theorem convolutionCoefficient_nil (ys : List R) (k : ℕ) :
    convolutionCoefficient [] ys k = 0 := rfl

@[simp] theorem convolutionCoefficient_cons_zero (a : R) (xs ys : List R) :
    convolutionCoefficient (a::xs) ys 0 = a * ys[0]?.getD 0 := by
  simp [convolutionCoefficient, List.zipIdx_cons, List.zipIdx_succ, List.map_map,
    Function.comp_def]

@[simp] theorem convolutionCoefficient_cons_succ (a : R) (xs ys : List R) (k : ℕ) :
    convolutionCoefficient (a::xs) ys (k+1) =
      a * ys[k+1]?.getD 0 + convolutionCoefficient xs ys k := by
  simp [convolutionCoefficient, List.zipIdx_cons, List.zipIdx_succ, List.map_map,
    Function.comp_def]

theorem convolutionCoefficient_eq (xs ys : List R) (k : ℕ) :
    convolutionCoefficient xs ys k = (polynomial xs * polynomial ys).coeff k := by
  induction xs generalizing k with
  | nil => simp [polynomial]
  | cons a xs ih =>
    have he : polynomial (a::xs) * polynomial ys =
        Polynomial.C a * polynomial ys + Polynomial.X * (polynomial xs * polynomial ys) := by
      rw [polynomial]; ring
    rw [he, Polynomial.coeff_add]
    cases k with
    | zero => simp [polynomial_coeff]
    | succ k => simp [ih, polynomial_coeff]

/-- One explicit trailing position avoids any normalization or degree test. -/
def convolution (xs ys : List R) : List R :=
  (List.range (xs.length + ys.length + 1)).map (convolutionCoefficient xs ys)

@[simp] theorem convolution_length (xs ys : List R) :
    (convolution xs ys).length = xs.length + ys.length + 1 := by simp [convolution]

theorem convolution_polynomial (xs ys : List R) :
    polynomial (convolution xs ys) = polynomial xs * polynomial ys := by
  ext k
  rw [polynomial_coeff]
  by_cases h : k < xs.length + ys.length + 1
  · simp only [convolution, List.getElem?_map, List.getElem?_range h,
      Option.map_some, Option.getD_some, convolutionCoefficient_eq]
  · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hh := (Polynomial.natDegree_mul_le (p := polynomial xs) (q := polynomial ys)).trans
      (Nat.add_le_add (polynomial_natDegree_le xs) (polynomial_natDegree_le ys))
    omega

end PlanarHom.CoefficientListAlgebra
