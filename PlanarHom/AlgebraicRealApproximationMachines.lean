import PlanarHom.AlgebraicRealApproximationAlgorithm
import PlanarHom.BoundedPolynomialEvaluationMachines

/-! # Actual polynomial-time approximation of each fixed algebraic real

The precision parameter is binary. A fixed rational sign interval and its fixed
polynomial are built into the program. Binary search over a rational grid uses
only exact rational arithmetic, polynomial evaluation and rational sign tests.
-/

noncomputable section
namespace PlanarHom.AlgebraicRealApproximationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BinaryArithmetic RationalCircuits AlgebraicRealApproximationAlgorithm

theorem fp_grid (l u : ℚ) : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.rat
    (fun p => grid l u p.1 p.2) := by
  have hN := (fp_fst BitEncoding.nat BitEncoding.nat).comp BoundedPolynomialEvaluationMachines.fp_natCast
  have ht := (fp_snd BitEncoding.nat BitEncoding.nat).comp BoundedPolynomialEvaluationMachines.fp_natCast
  have hm := ((fp_const (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.rat (u-l)).pair ht).comp
    fp_rational_multiplication
  have hd := (hm.pair hN).comp fp_rational_division
  exact ((fp_const (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.rat l).pair hd).comp
    fp_rational_addition

theorem fp_test (p : Polynomial ℚ) (l u : ℚ) :
    FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool (fun a => test p l u a.1 a.2) := by
  have he := BoundedPolynomialEvaluationMachines.fp_eval BitEncoding.nat (fun _ => p)
    p.natDegree (fun _ => le_rfl) (fun k => fp_const BitEncoding.nat BitEncoding.rat (p.coeff k))
  have hv := (((fp_fst BitEncoding.nat BitEncoding.nat).pair (fp_grid l u)).comp he)
  exact hv.comp RationalOrderMachines.fp_nonnegative

theorem fp_approximate (p : Polynomial ℚ) (l u : ℚ) :
    FP BitEncoding.nat BitEncoding.rat (approximate p l u) := by
  have hi := ((fp_id BitEncoding.nat).pair (fp_id BitEncoding.nat)).comp
    (IntervalBisection.fp_cut BitEncoding.nat (test p l u) (fp_test p l u))
  exact ((fp_id BitEncoding.nat).pair hi).comp (fp_grid l u)

/-- A genuine bit-machine approximation theorem. The fixed algebraic real is
program data; binary `N` requests error at most `1/(N+1)`. -/
theorem exists_fp_approximation (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ∃ f : ℕ → ℚ, FP BitEncoding.nat BitEncoding.rat f ∧
      ∀ N : ℕ, |(f N : ℝ)-a| ≤ 1/((N:ℝ)+1) := by
  obtain ⟨p, l, u, hl, hu, hs⟩ := AlgebraicRealSignInterval.exists_sign_interval a ha
  obtain ⟨L, hL⟩ := exists_nat_gt (max (((u-l:ℚ):ℝ)) 0)
  have hwidth : (((u-l:ℚ):ℝ)) ≤ (L:ℝ) := (le_max_left _ _).trans hL.le
  have hLp : (0:ℝ) < (L:ℝ) := (le_max_right _ _).trans_lt hL
  have hLpos : 0 < L := by exact_mod_cast hLp
  let f : ℕ → ℚ := fun N => approximate p l u (L*(N+1))
  refine ⟨f, ?_, ?_⟩
  · have hN := ((fp_const BitEncoding.nat BitEncoding.nat L).pair fp_successor).comp fp_multiplication
    exact hN.comp (fp_approximate p l u)
  · intro N
    have hprec : 0 < L*(N+1) := Nat.mul_pos hLpos (Nat.succ_pos _)
    have he := approximate_error p l u a hl hu hs (L*(N+1)) hprec
    change |(approximate p l u (L*(N+1)):ℝ)-a| ≤ _
    apply he.trans
    calc
      (((u-l:ℚ):ℝ))/((L*(N+1):ℕ):ℝ) ≤ (L:ℝ)/((L*(N+1):ℕ):ℝ) :=
        div_le_div_of_nonneg_right hwidth (by positivity)
      _ = 1/((N:ℝ)+1) := by
        have hLn : (L:ℝ) ≠ 0 := hLp.ne'
        push_cast
        field_simp

end PlanarHom.AlgebraicRealApproximationMachines
