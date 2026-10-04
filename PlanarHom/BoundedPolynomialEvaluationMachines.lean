import PlanarHom.PolynomialDiscretePartition
import PlanarHom.RationalOrderMachines
import PlanarHom.FiniteRationalCircuits

/-! # Actual evaluation and forward-difference circuits at fixed degree -/

noncomputable section
namespace PlanarHom.BoundedPolynomialEvaluationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open RationalCircuits BinaryArithmetic PolynomialDiscretePartition
open scoped BigOperators

theorem fp_ratPower (k : ℕ) : FP BitEncoding.rat BitEncoding.rat (fun q : ℚ => q^k) := by
  induction k with
  | zero => simpa using fp_const BitEncoding.rat BitEncoding.rat 1
  | succ k ih =>
    exact ((ih.pair (fp_id BitEncoding.rat)).comp fp_rational_multiplication).congr
      (fun q => (pow_succ q k).symm)

theorem fp_natCast : FP BitEncoding.nat BitEncoding.rat (fun n : ℕ => (n : ℚ)) :=
  (fp_nat_int.comp fp_int_rat).congr (fun _ => by simp)

theorem fp_eval {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP (ea.prod BitEncoding.rat) BitEncoding.rat (fun a => (p a.1).eval a.2) := by
  have hx := fp_fst ea BitEncoding.rat
  have ht := fp_snd ea BitEncoding.rat
  have hf (k : ℕ) := ((hx.comp (hc k)).pair (ht.comp (fp_ratPower k))).comp fp_rational_multiplication
  exact (FiniteRationalCircuits.fp_sum _ (Finset.range (d+1))
    (fun a k => (p a.1).coeff k * a.2^k) hf).congr
    (fun a => (Polynomial.eval_eq_sum_range' (by have := hd a.1; omega) a.2).symm)

theorem fp_values {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP (ea.prod BitEncoding.nat) BitEncoding.rat (fun a => values (p a.1) a.2) :=
  (((fp_fst ea BitEncoding.nat).pair
    ((fp_snd ea BitEncoding.nat).comp fp_natCast)).comp (fp_eval ea p d hd hc))

theorem difference_coeff (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) (k : ℕ) :
    (difference p).coeff k = ∑ j ∈ Finset.range (d+1),
      p.coeff j * (difference (Polynomial.X^j)).coeff k := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < d+1 by omega)]
  simp only [difference, map_sum, Polynomial.coeff_sub, Polynomial.finset_sum_coeff,
    ← Polynomial.smul_eq_C_mul, map_smul, Polynomial.coeff_smul, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fp_difference_coeff {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) (k : ℕ) :
    FP ea BitEncoding.rat (fun a => (difference (p a)).coeff k) := by
  have hf (j : ℕ) := ((hc j).pair (fp_const ea BitEncoding.rat
    ((difference (Polynomial.X^j)).coeff k))).comp fp_rational_multiplication
  exact (FiniteRationalCircuits.fp_sum ea (Finset.range (d+1))
    (fun a j => (p a).coeff j * (difference (Polynomial.X^j)).coeff k) hf).congr
      (fun a => (difference_coeff (p a) d (hd a) k).symm)

end PlanarHom.BoundedPolynomialEvaluationMachines
