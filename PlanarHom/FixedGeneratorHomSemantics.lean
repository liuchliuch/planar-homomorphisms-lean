import PlanarHom.FixedGeneratorPolynomialEvaluation

/-! NEW: fixed generator substitution realizes every given homomorphism from
the source polynomial ring. Generator images are finitely many fixed constants. -/
noncomputable section
namespace PlanarHom.FixedGeneratorEvaluation
open DensePolynomial
variable {d e : ℕ} {E : Type} [Field E] [Algebra (RationalFunction d) E]

def variablePoly : (m : ℕ) → Fin m → Poly m
  | 0,i => i.elim0
  | m+1,i => Fin.cases Polynomial.X (fun j => Polynomial.C (variablePoly m j)) i

@[simp] theorem variablePoly_zero (m : ℕ) : variablePoly (m+1) 0 = Polynomial.X := rfl
@[simp] theorem variablePoly_succ (m : ℕ) (i : Fin m) :
    variablePoly (m+1) i.succ = Polynomial.C (variablePoly m i) := rfl

theorem evalHom_eq (m : ℕ) (f : Poly m →+* E) :
    evalHom (d := d) m (fun i => f (variablePoly m i)) = f := by
  induction m with
  | zero =>
    ext q
    exact (eq_ratCast _ q).trans (eq_ratCast f q).symm
  | succ m ih =>
    apply Polynomial.ringHom_ext
    · intro a
      rw [evalHom,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
      exact DFunLike.congr_fun (ih (f.comp Polynomial.C)) a
    · simp [evalHom,Polynomial.coe_eval₂RingHom,variablePoly]
      rfl

theorem evaluate_hom (basis : Module.Basis (Fin e) (RationalFunction d) E)
    (m : ℕ) (f : Poly m →+* E) (p : DensePolynomial.Code m) :
    FixedRealExtension.value basis (evaluate basis m (fun i => f (variablePoly m i)) p) =
      f (interpret m p) := by
  rw [evaluate_value, evalHom_eq]

end PlanarHom.FixedGeneratorEvaluation
