import PlanarHom.MatrixLogCoefficients
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Matrix-entry orders and off-diagonal logarithmic leading terms

The multiplication lemmas retain the better off-diagonal order even when the
diagonal perturbation has only first order. This is the distinction needed for
entrywise even powers in Lemmas 4.1 and 4.3.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluating an entry is continuous and linear for the matrix operator norm. -/
def entryCLM (i j : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

omit [DecidableEq V] in
@[simp] theorem entryCLM_apply (i j : V) (A : Matrix V V ℝ) : entryCLM i j A = A i j := rfl

/-- An operator-norm order estimate bounds each matrix entry. -/
theorem entry_isBigO {α : Type*} {l : Filter α} {Q : α → Matrix V V ℝ}
    {g : α → ℝ} (hQ : Q =O[l] g) (i j : V) : (fun t => Q t i j) =O[l] g :=
  ((entryCLM i j).isBigO_comp Q l).trans hQ

/-- A higher nonnegative integral power vanishes at least as fast near zero. -/
theorem pow_isBigO_pow {m n : ℕ} (hmn : m ≤ n) :
    (fun t : ℝ => t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ m) := by
  apply IsBigO.of_bound 1
  have hs : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖ < 1 := by
    simpa only [Metric.ball, dist_zero_right, Set.mem_setOf_eq] using
      (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
  filter_upwards [hs] with t ht
  simpa only [one_mul, norm_pow] using pow_le_pow_of_le_one (norm_nonneg t) ht.le hmn

/-- For `Q=O(t)`, an off-diagonal entry of `Q^n` needs at least one
off-diagonal factor, so it has order at least `s+n-1`. -/
theorem pow_entry_offDiagonal_isBigO (Q : ℝ → Matrix V V ℝ) (s : ℕ)
    (hQ : Q =O[𝓝 0] (fun t : ℝ => t))
    (hoff : ∀ i j, i ≠ j → (fun t => Q t i j) =O[𝓝 0] (fun t : ℝ => t ^ s))
    (n : ℕ) (i j : V) (hij : i ≠ j) :
    (fun t => (Q t ^ (n + 1)) i j) =O[𝓝 0] (fun t : ℝ => t ^ (s + n)) := by
  induction n with
  | zero => simpa using hoff i j hij
  | succ n ih =>
    have hterm : ∀ k : V,
        (fun t => (Q t ^ (n + 1)) i k * Q t k j) =O[𝓝 0]
          (fun t : ℝ => t ^ (s + (n + 1))) := by
      intro k
      by_cases hkj : k = j
      · subst k
        convert ih.mul (entry_isBigO hQ j j) using 1
      · have hp := entry_isBigO (hQ.pow (n + 1)) i k
        have h := hp.mul (hoff k j hkj)
        convert h using 1
        ext t
        rw [← pow_add]
        congr 1
        omega
    have hsum := IsBigO.sum (s := Finset.univ) (fun k _ => hterm k)
    simpa only [pow_succ _ (n + 1), Matrix.mul_apply] using hsum

/-- Entrywise order estimates combine into an operator-norm estimate. -/
theorem matrix_isBigO_of_entries {α : Type*} {l : Filter α} (Q : α → Matrix V V ℝ)
    (g : α → ℝ) (hQ : ∀ i j, (fun t => Q t i j) =O[l] g) : Q =O[l] g := by
  let S : V → V → ℝ →L[ℝ] Matrix V V ℝ := fun i j =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Matrix.single i j 1)
  have hsingle : ∀ i j, (fun t => Matrix.single i j (Q t i j)) =O[l] g := by
    intro i j
    have h := ((S i j).isBigO_comp (fun t => Q t i j) l).trans (hQ i j)
    convert h using 1
    ext t a b
    simp [S, Matrix.single, Matrix.of_apply]
  have h := IsBigO.sum (s := Finset.univ) (fun i _ =>
    IsBigO.sum (s := Finset.univ) (fun j _ => hsingle i j))
  exact h.congr_left (fun t => (Matrix.matrix_eq_sum_single (Q t)).symm)

/-- Raising a scalar first-order expansion to any natural power gives its
actual leading coefficient and an error of one higher order. -/
theorem pow_sub_leading_isBigO (f : ℝ → ℝ) (a : ℝ)
    (hf : f =O[𝓝 0] (fun t : ℝ => t))
    (hrem : (fun t => f t - a * t) =O[𝓝 0] (fun t : ℝ => t ^ 2)) (s : ℕ) :
    (fun t => f t ^ s - a ^ s * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
  have ha : (fun t : ℝ => a * t) =O[𝓝 0] (fun t : ℝ => t) :=
    (isBigO_refl _ _).const_mul_left a
  induction s with
  | zero => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | succ s ih =>
    have h₁ := hf.mul ih
    have h₂ := hrem.mul (ha.pow s)
    have h₁' : (fun t => f t * (f t ^ s - a ^ s * t ^ s)) =O[𝓝 0]
        (fun t : ℝ => t ^ (s + 1 + 1)) := by
      convert h₁ using 1
      ext t
      ring
    have h₂' : (fun t => (f t - a * t) * (a * t) ^ s) =O[𝓝 0]
        (fun t : ℝ => t ^ (s + 1 + 1)) := by
      convert h₂ using 1
      ext t
      ring
    convert h₁'.add h₂' using 1
    ext t
    simp only [pow_succ, mul_pow]
    ring

variable [Nonempty V]

/-- The correction made by the finite log polynomial has an extra order at
every off-diagonal entry. Diagonal terms may still have order one. -/
theorem logTaylor_sub_self_offDiagonal_isBigO (Q : ℝ → Matrix V V ℝ) (s n : ℕ)
    (hQ : Q =O[𝓝 0] (fun t : ℝ => t))
    (hoff : ∀ i j, i ≠ j → (fun t => Q t i j) =O[𝓝 0] (fun t : ℝ => t ^ s))
    (i j : V) (hij : i ≠ j) :
    (fun t => (logTaylor (Q t) (n + 1) - Q t) i j) =O[𝓝 0]
      (fun t : ℝ => t ^ (s + 1)) := by
  induction n with
  | zero => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t ^ (s + 1)) (𝓝 0))
  | succ n ih =>
    have hp : (fun t => (Q t ^ (n + 2)) i j) =O[𝓝 0]
        (fun t : ℝ => t ^ (s + 1)) :=
      (pow_entry_offDiagonal_isBigO Q s hQ hoff (n + 1) i j hij).trans
        (pow_isBigO_pow (by omega))
    have hterm := hp.const_mul_left (-(((n + 2 : ℕ) : ℝ)⁻¹ * (-1 : ℝ) ^ (n + 2)))
    convert ih.add hterm using 1
    ext t
    have hneg : (-Q t) ^ (n + 2) = (-1 : ℝ) ^ (n + 2) • Q t ^ (n + 2) := by
      rw [← neg_one_smul ℝ (Q t), smul_pow]
    simp only [logTaylor, Finset.sum_range_succ, neg_add, Matrix.sub_apply,
      Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show n + 1 + 1 = n + 2 by omega, hneg]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring

/-- The actual matrix logarithm keeps every leading off-diagonal coefficient.
The hypotheses concern only the input perturbation, not the logarithm. -/
theorem matrixLog_sub_self_offDiagonal_isBigO (Q : ℝ → Matrix V V ℝ) (s : ℕ)
    (hs : 0 < s) (hherm : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian)
    (hzero : Tendsto Q (𝓝 0) (𝓝 0))
    (hQ : Q =O[𝓝 0] (fun t : ℝ => t))
    (hoff : ∀ i j, i ≠ j → (fun t => Q t i j) =O[𝓝 0] (fun t : ℝ => t ^ s))
    (i j : V) (hij : i ≠ j) :
    (fun t => EntropyCompletion.matrixLog (1 + Q t) i j - Q t i j) =O[𝓝 0]
      (fun t : ℝ => t ^ (s + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hr := entry_isBigO
    (matrixLog_sub_logTaylor_isBigO_pow Q hherm hzero 1 (n + 1) (by simpa using hQ)) i j
  have hp := logTaylor_sub_self_offDiagonal_isBigO Q (n + 1) n hQ hoff i j hij
  simp only [Nat.one_mul] at hr
  have h := hr.add hp
  simpa only [Nat.one_mul, Matrix.sub_apply, sub_add_sub_cancel] using h

end PlanarHom.MatrixLogCoefficients
