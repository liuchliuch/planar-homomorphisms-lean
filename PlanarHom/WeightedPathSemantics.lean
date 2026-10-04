import PlanarHom.PathPowerSemantics

/-! Exact weighted chains for source3.7. Each private vertex contributes its
background weight once; the endpoints contribute no weights to the signature. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PathPower
variable {C R : Type*} [Fintype C] [DecidableEq C] [CommSemiring R]

def weightedWeight (n : ℕ) (M : Matrix C C R) (w : C → R) (x y : C) (τ : Fin n → C) : R :=
  (∏ k, w (τ k)) * weight n M x y τ

@[simp] theorem weightedWeight_zero (M : Matrix C C R) (w : C → R) (x y : C) (τ : Fin 0 → C) :
    weightedWeight 0 M w x y τ = M x y := by simp [weightedWeight]

theorem weightedWeight_cons (n : ℕ) (M : Matrix C C R) (w : C → R)
    (x y z : C) (τ : Fin n → C) :
    weightedWeight (n+1) M w x y (Fin.cons z τ) =
      M x z * w z * weightedWeight n M w z y τ := by
  simp only [weightedWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,weight_cons]
  ring

/-- This is the weighted path formula K(DK)^(h−1), valid for h=n+1 and arbitrary
commutative semiring weights, including zero or signed specializations. -/
theorem sum_weightedWeight (n : ℕ) (M : Matrix C C R) (w : C → R) (x y : C) :
    (∑ τ : Fin n → C, weightedWeight n M w x y τ) =
      (M * (Matrix.diagonal w * M)^n) x y := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∑ p : C × (Fin n → C), weightedWeight (n+1) M w x y (Fin.cons p.1 p.2) := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => C)).symm
        intro τ
        simp
      _ = ∑ z : C, ∑ τ : Fin n → C, M x z * w z * weightedWeight n M w z y τ := by
        rw [Fintype.sum_prod_type]
        simp only [weightedWeight_cons]
      _ = ∑ z : C, (M x z * w z) * (M * (Matrix.diagonal w * M)^n) z y := by
        simp only [← Finset.mul_sum,ih]
      _ = ((M * Matrix.diagonal w) * (M * (Matrix.diagonal w * M)^n)) x y := by
        conv_rhs => rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal]
      _ = (M * (Matrix.diagonal w * M)^(n+1)) x y := by
        rw [pow_succ']
        simp only [Matrix.mul_assoc]

end PlanarHom.PathPower
