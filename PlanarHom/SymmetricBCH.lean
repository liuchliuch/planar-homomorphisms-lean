import PlanarHom.MatrixCubicApproximation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-!
# The genuine symmetric BCH cubic term

A third-order expansion of the actual exponential sandwich is combined with
the actual spectral logarithm Taylor remainder. Matrix products retain their
noncommutative order. This is the coefficient calculation in Proposition 4.8.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.SymmetricBCH
open MatrixLogCoefficients MatrixCubicApproximation
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary matrix commutator. -/
def commutator (A B : Matrix V V ℝ) : Matrix V V ℝ := A * B - B * A

/-- The actual symmetric product of three matrix exponentials. -/
def sandwich (C B : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C)) * NormedSpace.exp ℝ (t • B) *
    NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C))

/-- The degree-three coefficient before taking the logarithm. -/
def thirdCoefficient (C B : Matrix V V ℝ) : Matrix V V ℝ :=
  (1 / 6 : ℝ) • C ^ 3 + (1 / 8 : ℝ) • (C ^ 2 * B + B * C ^ 2) +
    (1 / 4 : ℝ) • (C * B * C) + (1 / 4 : ℝ) • (C * B ^ 2 + B ^ 2 * C) +
    (1 / 6 : ℝ) • B ^ 3

/-- The symmetric BCH correction, with its actual ordered double commutators. -/
def cubicCorrection (C B : Matrix V V ℝ) : Matrix V V ℝ :=
  (-1 / 24 : ℝ) • commutator C (commutator C B) +
    (1 / 12 : ℝ) • commutator B (commutator B C)

/-- Exact noncommutative algebra identifies the cubic logarithmic coefficient. -/
theorem thirdCoefficient_sub_cube (C B : Matrix V V ℝ) :
    thirdCoefficient C B - (1 / 6 : ℝ) • (C + B) ^ 3 = cubicCorrection C B := by
  simp only [thirdCoefficient, cubicCorrection, commutator, pow_succ, pow_zero,
    one_mul, mul_one, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, mul_assoc]
  module

/-- The actual exponential sandwich has its cubic expansion, with an operator
norm fourth-order error. -/
theorem sandwich_cubic_remainder_isBigO (C B : Matrix V V ℝ) :
    (fun t => sandwich C B t -
      cubic 1 (C + B) ((1 / 2 : ℝ) • (C + B) ^ 2) (thirdCoefficient C B) t)
      =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
  let H := (1 / 2 : ℝ) • C
  let H₂ := (1 / 2 : ℝ) • H ^ 2
  let H₃ := (1 / 6 : ℝ) • H ^ 3
  let B₂ := (1 / 2 : ℝ) • B ^ 2
  let B₃ := (1 / 6 : ℝ) • B ^ 3
  have hh := exp_cubic_remainder_isBigO H
  have hb := exp_cubic_remainder_isBigO B
  have hp := mul_cubic_remainder_isBigO 1 H H₂ H₃ 1 B B₂ B₃ hh hb
  have hpp := mul_cubic_remainder_isBigO (1 * 1) (1 * B + H * 1)
    (1 * B₂ + H * B + H₂ * 1) (1 * B₃ + H * B₂ + H₂ * B + H₃ * 1)
    1 H H₂ H₃ hp hh
  convert hpp using 1
  funext t
  change sandwich C B t - _ = sandwich C B t - _
  congr 1
  simp only [cubic, thirdCoefficient, H, H₂, H₃, B₂, B₃, pow_succ, pow_zero,
    one_mul, mul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, mul_assoc]
  module

/-- Hermitian inputs give a Hermitian sandwich, without a commutation hypothesis. -/
theorem sandwich_isHermitian (C B : Matrix V V ℝ) (hC : C.IsHermitian)
    (hB : B.IsHermitian) (t : ℝ) : (sandwich C B t).IsHermitian := by
  have hc : IsSelfAdjoint (t • ((1 / 2 : ℝ) • C)) := by
    change star (t • ((1 / 2 : ℝ) • C)) = _
    simp only [star_smul, star_trivial]
    rw [show star C = C from hC]
  have hb : IsSelfAdjoint (t • B) := by
    change star (t • B) = _
    simp only [star_smul, star_trivial]
    rw [show star B = B from hB]
  have hec := hc.exp ℝ
  have heb := hb.exp ℝ
  change star (NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C))) = _ at hec
  change star (NormedSpace.exp ℝ (t • B)) = _ at heb
  change star (sandwich C B t) = sandwich C B t
  simp only [sandwich, star_mul, hec, heb, mul_assoc]

@[simp] theorem sandwich_zero (C B : Matrix V V ℝ) : sandwich C B 0 = 1 := by
  simp [sandwich]

/-- The sandwich is a first-order perturbation of the identity. -/
theorem sandwich_sub_one_isBigO (C B : Matrix V V ℝ) :
    (fun t => sandwich C B t - 1) =O[𝓝 0] (fun t : ℝ => t) := by
  have hh := (hasFDerivAt_exp_smul_const ℝ ((1 / 2 : ℝ) • C) (0 : ℝ)).differentiableAt
  have hb := (hasFDerivAt_exp_smul_const ℝ B (0 : ℝ)).differentiableAt
  have h := ((hh.mul hb).mul hh).hasFDerivAt.isBigO_sub
  simpa [sandwich] using h

/-- The third logarithm polynomial, stated in the usual signed form. -/
theorem logTaylor_three (Q : Matrix V V ℝ) :
    logTaylor Q 3 = Q - (1 / 2 : ℝ) • Q ^ 2 + (1 / 3 : ℝ) • Q ^ 3 := by
  norm_num [logTaylor, Finset.sum_range_succ, pow_succ]
  module

variable [Nonempty V]

/-- Cubic coefficient extraction for the genuine spectral logarithm of any
Hermitian perturbation with the specified input expansion. -/
theorem matrixLog_of_cubic_remainder_isBigO (Q : ℝ → Matrix V V ℝ)
    (X Y : Matrix V V ℝ)
    (hherm : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian)
    (horder : Q =O[𝓝 0] (fun t : ℝ => t))
    (hcoeff : (fun t => Q t - cubic 0 X ((1 / 2 : ℝ) • X ^ 2) Y t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4)) :
    (fun t => EntropyCompletion.matrixLog (1 + Q t) -
      cubic 0 X 0 (Y - (1 / 6 : ℝ) • X ^ 3) t) =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
  let D := (1 / 2 : ℝ) • X ^ 2
  have hmul := mul_cubic_remainder_isBigO 0 X D Y 0 X D Y hcoeff hcoeff
  have hQ₂ : (fun t => Q t ^ 2 - cubic 0 0 (X ^ 2) (X ^ 3) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
    convert hmul using 1
    funext t
    simp only [cubic, D, pow_succ, pow_zero, one_mul, mul_one, zero_mul, mul_zero,
      add_zero, zero_add, smul_zero, zero_smul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, smul_add, mul_assoc]
    module
  have hmul₃ := mul_cubic_remainder_isBigO 0 0 (X ^ 2) (X ^ 3) 0 X D Y hQ₂ hcoeff
  have hQ₃ : (fun t => Q t ^ 3 - cubic 0 0 0 (X ^ 3) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
    convert hmul₃ using 1
    funext t
    simp only [cubic, D, pow_succ, pow_zero, one_mul, mul_one, zero_mul, mul_zero,
      add_zero, zero_add, smul_zero, zero_smul, mul_assoc]
  have hcomb := (hcoeff.sub (hQ₂.const_smul_left (1 / 2 : ℝ))).add
    (hQ₃.const_smul_left (1 / 3 : ℝ))
  have hpoly : (fun t => logTaylor (Q t) 3 -
      cubic 0 X 0 (Y - (1 / 6 : ℝ) • X ^ 3) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
    convert hcomb using 1
    funext t
    rw [logTaylor_three]
    simp only [cubic, Pi.smul_apply, smul_add, smul_sub, smul_smul, smul_zero,
      zero_smul, zero_add, add_zero]
    module
  have hz : Tendsto Q (𝓝 0) (𝓝 0) := horder.trans_tendsto tendsto_id
  have hlog := matrixLog_sub_logTaylor_isBigO_pow Q hherm hz 1 3 (by simpa using horder)
  have h := hlog.add hpoly
  simpa only [Nat.one_mul, Nat.reduceAdd, sub_add_sub_cancel] using h

/-- The true symmetric BCH cubic expansion with a rigorous operator-norm
fourth-order remainder. -/
theorem matrixLog_sandwich_cubic_remainder_isBigO (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) :
    (fun t => EntropyCompletion.matrixLog (sandwich C B t) -
      (t • (C + B) + t ^ 3 • cubicCorrection C B)) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
  let Q : ℝ → Matrix V V ℝ := fun t => sandwich C B t - 1
  have hherm : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian := Eventually.of_forall fun t =>
    (sandwich_isHermitian C B hC hB t).sub Matrix.isHermitian_one
  have horder : Q =O[𝓝 0] (fun t : ℝ => t) := sandwich_sub_one_isBigO C B
  have hcoeff : (fun t => Q t -
      cubic 0 (C + B) ((1 / 2 : ℝ) • (C + B) ^ 2) (thirdCoefficient C B) t)
      =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
    convert sandwich_cubic_remainder_isBigO C B using 1
    funext t
    simp only [Q, cubic, zero_add]
    abel
  have h := matrixLog_of_cubic_remainder_isBigO Q (C + B) (thirdCoefficient C B)
    hherm horder hcoeff
  have heq : ∀ t, 1 + Q t = sandwich C B t := by intro t; dsimp [Q]; abel
  simpa only [heq, thirdCoefficient_sub_cube, cubic, zero_add, smul_zero, add_zero] using h

/-- Scaling the middle direction separates the linear and quadratic sector parameters. -/
theorem cubicCorrection_smul_right (C B : Matrix V V ℝ) (η : ℝ) :
    cubicCorrection C (η • B) =
      (-η / 24) • commutator C (commutator C B) +
      (η ^ 2 / 12) • commutator B (commutator B C) := by
  simp only [cubicCorrection, commutator, mul_sub, sub_mul, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_smul]
  module

/-- One-variable sector form of the genuine symmetric BCH expansion. Its
coefficient linear in `η` is exactly `-[C,[C,B]]/24`. -/
theorem matrixLog_symmetric_sector_cubic_remainder_isBigO (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (η : ℝ) :
    (fun t => EntropyCompletion.matrixLog (sandwich C (η • B) t) -
      (t • (C + η • B) + t ^ 3 •
        ((-η / 24) • commutator C (commutator C B) +
          (η ^ 2 / 12) • commutator B (commutator B C)))) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
  have hηB : (η • B).IsHermitian := by
    change star (η • B) = η • B
    rw [star_smul, star_trivial]
    exact congrArg (fun A : Matrix V V ℝ => η • A) hB
  simpa only [cubicCorrection_smul_right] using
    matrixLog_sandwich_cubic_remainder_isBigO C (η • B) hC hηB

/-- The sector curve is exactly the source's three-exponential matrix product. -/
theorem sandwich_sector_eq (C B : Matrix V V ℝ) (η t : ℝ) :
    sandwich C (η • B) t =
      NormedSpace.exp ℝ ((t / 2) • C) * NormedSpace.exp ℝ ((η * t) • B) *
        NormedSpace.exp ℝ ((t / 2) • C) := by
  simp only [sandwich, smul_smul, div_eq_mul_inv]
  rw [mul_comm t η]
  norm_num

end PlanarHom.SymmetricBCH
