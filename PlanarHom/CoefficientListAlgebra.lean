import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.Enum
import Mathlib.Tactic.Ring

/-! Polynomial coefficient lists over commutative rings, allowing zero divisors
and explicit trailing zeros. Synthetic division uses no division in the ring. -/
namespace PlanarHom.CoefficientListAlgebra
variable {R : Type} [CommRing R]

noncomputable def polynomial : List R → Polynomial R
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * polynomial cs

def evaluate (b : R) (cs : List R) : R :=
  (cs.zipIdx.map (fun p => p.1 * b ^ p.2)).sum

theorem shifted_sum (b : R) (cs : List R) (j : ℕ) :
    ((cs.zipIdx j).map (fun p => p.1 * b ^ p.2)).sum =
      b ^ j * (polynomial cs).eval b := by
  induction cs generalizing j with
  | nil => simp [polynomial]
  | cons c cs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih, polynomial,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, pow_succ]
    ring

theorem evaluate_eq (b : R) (cs : List R) :
    evaluate b cs = (polynomial cs).eval b := by
  simpa [evaluate] using shifted_sum b cs 0

@[simp] theorem evaluate_nil (b : R) : evaluate b [] = 0 := by simp [evaluate]

@[simp] theorem evaluate_cons (b c : R) (cs : List R) :
    evaluate b (c :: cs) = c + b * evaluate b cs := by
  simp [evaluate_eq, polynomial]

/-- The final zero is retained; this makes every output position an actual
indexed evaluation of a strict suffix of the input coefficient list. -/
def quotientCoefficients (b : R) (cs : List R) : List R :=
  cs.zipIdx.map (fun p => evaluate b (cs.drop (p.2 + 1)))

@[simp] theorem quotientCoefficients_nil (b : R) : quotientCoefficients b [] = [] := rfl

@[simp] theorem quotientCoefficients_cons (b c : R) (cs : List R) :
    quotientCoefficients b (c :: cs) = evaluate b cs :: quotientCoefficients b cs := by
  simp only [quotientCoefficients, List.zipIdx_cons, List.map_cons, Nat.zero_add,
    List.drop_succ_cons, List.drop_zero]
  congr 1
  rw [List.zipIdx_succ, List.map_map]
  rfl

@[simp] theorem quotientCoefficients_length (b : R) (cs : List R) :
    (quotientCoefficients b cs).length = cs.length := by
  simp [quotientCoefficients]

/-- Exact polynomial division identity over an arbitrary commutative ring. -/
theorem quotient_identity (b : R) (cs : List R) :
    (Polynomial.X - Polynomial.C b) * polynomial (quotientCoefficients b cs) =
      polynomial cs - Polynomial.C (evaluate b cs) := by
  induction cs with
  | nil => simp [polynomial]
  | cons c cs ih =>
    rw [quotientCoefficients_cons, polynomial, polynomial, evaluate_cons]
    rw [Polynomial.C_add, Polynomial.C_mul]
    calc
      _ = Polynomial.X * ((Polynomial.X - Polynomial.C b) *
        polynomial (quotientCoefficients b cs)) +
        (Polynomial.X - Polynomial.C b) * Polynomial.C (evaluate b cs) := by ring
      _ = _ := by rw [ih]; ring

/-- The executable suffix construction represents the library monic quotient. -/
theorem quotient_polynomial (b : R) (cs : List R) :
    polynomial (quotientCoefficients b cs) =
      polynomial cs /ₘ (Polynomial.X - Polynomial.C b) := by
  have h := Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic (polynomial cs) b
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, ← evaluate_eq] at h
  have he := (quotient_identity b cs).trans h.symm
  have hd := congrArg (fun p : Polynomial R => p /ₘ (Polynomial.X - Polynomial.C b)) he
  simpa only [Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C b)] using hd

end PlanarHom.CoefficientListAlgebra
