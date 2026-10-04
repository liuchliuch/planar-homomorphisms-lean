import PlanarHom.SymmetricBCH
import PlanarHom.ShortestPathWeights

/-!
# Schur powers of general Hermitian identity perturbations

A genuine matrix curve with first-order coefficient `A` has off-diagonal
Schur-log coefficient `Aᵢⱼ^s`. This extends the earlier exponential-only result
to the symmetric sandwich used for support containment in Proposition 4.8.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients

/-- Scalar powers of a first-order perturbation of one remain first-order. -/
theorem pow_sub_one_isBigO {f : ℝ → ℝ}
    (hf : (fun t => f t - 1) =O[𝓝 0] (fun t : ℝ => t)) (s : ℕ) :
    (fun t => f t ^ s - 1) =O[𝓝 0] (fun t : ℝ => t) := by
  have hrem := hf.trans (by simpa only [pow_one, pow_zero] using
    (pow_isBigO_pow (show 0 ≤ 1 by omega)))
  have hbound : f =O[𝓝 0] (fun _t : ℝ => (1 : ℝ)) := by
    simpa only [sub_add_cancel] using hrem.add
      (isBigO_refl (fun _t : ℝ => (1 : ℝ)) (𝓝 0))
  induction s with
  | zero => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | succ s ih =>
    have hm := ih.mul hbound
    simp only [mul_one] at hm
    have h := hm.add hf
    convert h using 1
    funext t
    rw [pow_succ]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual entrywise powers along an arbitrary matrix curve. -/
def schurCurve (F : ℝ → Matrix V V ℝ) (s : ℕ) (t : ℝ) : Matrix V V ℝ :=
  ShortestPathWeights.entrywisePow (F t) s

/-- Entrywise powers preserve a first-order perturbation of the identity. -/
theorem schurCurve_sub_one_isBigO (F : ℝ → Matrix V V ℝ) (s : ℕ) (hs : 0 < s)
    (hF : (fun t => F t - 1) =O[𝓝 0] (fun t : ℝ => t)) :
    (fun t => schurCurve F s t - 1) =O[𝓝 0] (fun t : ℝ => t) := by
  apply matrix_isBigO_of_entries
  intro i j
  by_cases hij : i = j
  · subst j
    have hdiag : (fun t => F t i i - 1) =O[𝓝 0] (fun t : ℝ => t) := by
      simpa only [Matrix.sub_apply, Matrix.one_apply_eq] using entry_isBigO hF i i
    simpa only [schurCurve, ShortestPathWeights.entrywisePow, Matrix.sub_apply,
      Matrix.one_apply_eq] using pow_sub_one_isBigO hdiag s
  · have he : (fun t => F t i j) =O[𝓝 0] (fun t : ℝ => t) := by
      simpa only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] using entry_isBigO hF i j
    simpa only [schurCurve, ShortestPathWeights.entrywisePow, Matrix.sub_apply,
      Matrix.one_apply_ne hij, sub_zero, pow_one] using
      (he.pow s).trans (pow_isBigO_pow hs)

/-- Entrywise powers of a real Hermitian matrix remain Hermitian. -/
theorem schurCurve_isHermitian (F : ℝ → Matrix V V ℝ) (s : ℕ) (t : ℝ)
    (hF : (F t).IsHermitian) : (schurCurve F s t).IsHermitian := by
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial, schurCurve,
    ShortestPathWeights.entrywisePow] using congrArg (fun x : ℝ => x ^ s) (hF.apply i j)

variable [Nonempty V]

/-- The actual off-diagonal logarithmic coefficient for any Hermitian curve
with a proved first-order expansion. -/
theorem matrixLog_schurCurve_entry_sub_leading_isBigO
    (F : ℝ → Matrix V V ℝ) (s : ℕ) (hs : 0 < s)
    (hherm : ∀ᶠ t in 𝓝 0, (F t).IsHermitian)
    (hF : (fun t => F t - 1) =O[𝓝 0] (fun t : ℝ => t))
    (i j : V) (hij : i ≠ j) (a : ℝ)
    (hlead : (fun t => F t i j - a * t) =O[𝓝 0] (fun t : ℝ => t ^ 2)) :
    (fun t => EntropyCompletion.matrixLog (schurCurve F s t) i j - a ^ s * t ^ s)
      =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
  let Q : ℝ → Matrix V V ℝ := fun t => schurCurve F s t - 1
  have hQ : Q =O[𝓝 0] (fun t : ℝ => t) := schurCurve_sub_one_isBigO F s hs hF
  have hz : Tendsto Q (𝓝 0) (𝓝 0) := hQ.trans_tendsto tendsto_id
  have hh : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian := hherm.mono fun t ht =>
    (schurCurve_isHermitian F s t ht).sub Matrix.isHermitian_one
  have hoff : ∀ u v, u ≠ v → (fun t => Q t u v) =O[𝓝 0] (fun t : ℝ => t ^ s) := by
    intro u v huv
    have he : (fun t => F t u v) =O[𝓝 0] (fun t : ℝ => t) := by
      simpa only [Matrix.sub_apply, Matrix.one_apply_ne huv, sub_zero] using entry_isBigO hF u v
    simpa only [Q, schurCurve, ShortestPathWeights.entrywisePow, Matrix.sub_apply,
      Matrix.one_apply_ne huv, sub_zero] using he.pow s
  have hlog := matrixLog_sub_self_offDiagonal_isBigO Q s hs hh hz hQ hoff i j hij
  have he : (fun t => F t i j) =O[𝓝 0] (fun t : ℝ => t) := by
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] using entry_isBigO hF i j
  have hp := pow_sub_leading_isBigO (fun t => F t i j) a he hlead s
  have heq : ∀ t, 1 + Q t = schurCurve F s t := by intro t; dsimp [Q]; abel
  have hlog' : (fun t => EntropyCompletion.matrixLog (schurCurve F s t) i j -
      (F t i j) ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
    apply hlog.congr_left
    intro t
    rw [heq]
    simp only [Q, Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero,
      schurCurve, ShortestPathWeights.entrywisePow]
  simpa only [sub_add_sub_cancel] using hlog'.add hp

end PlanarHom.MatrixLogCoefficients

namespace PlanarHom.SymmetricBCH
open MatrixLogCoefficients MatrixCubicApproximation
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual symmetric sandwich has first-order coefficient `C+B` at each nonedge. -/
theorem sandwich_entry_sub_linear_isBigO (C B : Matrix V V ℝ) (i j : V) (hij : i ≠ j) :
    (fun t => sandwich C B t i j - (C + B) i j * t) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hr := (entry_isBigO (sandwich_cubic_remainder_isBigO C B) i j).trans
    (pow_isBigO_pow (show 2 ≤ 4 by omega))
  have h₂ := (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).const_mul_left
    (((1 / 2 : ℝ) • (C + B) ^ 2) i j)
  have h₃ := ((isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 0)).const_mul_left
    (thirdCoefficient C B i j)).trans (pow_isBigO_pow (show 2 ≤ 3 by omega))
  convert (hr.add h₂).add h₃ using 1
  funext t
  simp only [cubic, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply_ne hij]
  ring

variable [Nonempty V]

/-- The genuine Schur-square logarithm coefficient used to force logarithmic
support containment in the first step of Proposition 4.8. -/
theorem matrixLog_schur_square_sandwich_entry_sub_leading_isBigO
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (η : ℝ) (i j : V) (hij : i ≠ j) :
    (fun t => EntropyCompletion.matrixLog (schurCurve (sandwich C (η • B)) 2 t) i j -
      (C i j + η * B i j) ^ 2 * t ^ 2) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have hηB : (η • B).IsHermitian := by
    change star (η • B) = η • B
    rw [star_smul, star_trivial]
    exact congrArg (fun A : Matrix V V ℝ => η • A) hB
  have h := matrixLog_schurCurve_entry_sub_leading_isBigO (sandwich C (η • B)) 2
    (by omega) (Eventually.of_forall fun t => sandwich_isHermitian C (η • B) hC hηB t)
    (sandwich_sub_one_isBigO C (η • B)) i j hij ((C + η • B) i j)
    (sandwich_entry_sub_linear_isBigO C (η • B) i j hij)
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.reduceAdd] using h

/-- Every nonzero first-order sandwich edge becomes a positive logarithmic
edge after the actual Schur square. -/
theorem eventually_matrixLog_schur_square_sandwich_entry_pos
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (η : ℝ) (i j : V) (hij : i ≠ j) (hne : C i j + η * B i j ≠ 0) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      0 < EntropyCompletion.matrixLog (schurCurve (sandwich C (η • B)) 2 t) i j :=
  eventually_pos_of_positive_leading (sq_pos_of_ne_zero hne) 2
    (matrixLog_schur_square_sandwich_entry_sub_leading_isBigO C B hC hB η i j hij)

end PlanarHom.SymmetricBCH
