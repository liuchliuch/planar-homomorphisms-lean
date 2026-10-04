import PlanarHom.FixedFieldPowerRootCandidates
import PlanarHom.FixedRealFieldSign

/-! # Exact selection of the nonnegative power root in a fixed real field

The candidate generator verifies the power equation exactly. A real sign test
then retains positive roots; zero is the total default when no positive root
exists. Positive powers are injective on the nonnegative real half-line.
-/
noncomputable section
namespace PlanarHom.PositiveFieldPowerRootMachines
open Complexity FixedFieldPowerRootCandidates
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K) (embedding : K →+* ℝ)

def positiveRoots (n : ℕ) (y : K) : List K :=
  (roots basis n y).filter (fun x => decide (0 < embedding x))

def root (n : ℕ) (y : K) : K := (positiveRoots basis embedding n y).headD 0

theorem mem_positiveRoots_iff (n : ℕ) (hn : 0 < n) (x y : K) :
    x ∈ positiveRoots basis embedding n y ↔ x^n = y ∧ 0 < embedding x := by
  simp [positiveRoots, mem_roots_iff basis n hn]

theorem root_pow (n : ℕ) (hn : 0 < n) (x : K) (hx : 0 < embedding x) :
    root basis embedding n (x^n) = x := by
  have hmem : x ∈ positiveRoots basis embedding n (x^n) :=
    (mem_positiveRoots_iff basis embedding n hn x (x^n)).mpr ⟨rfl, hx⟩
  have hall (z : K) (hz : z ∈ positiveRoots basis embedding n (x^n)) : z = x := by
    obtain ⟨he, hz⟩ := (mem_positiveRoots_iff basis embedding n hn z (x^n)).mp hz
    apply embedding.injective
    apply (pow_left_inj₀ hz.le hx.le hn.ne').mp
    simpa only [map_pow] using congrArg embedding he
  unfold root
  cases h : positiveRoots basis embedding n (x^n) with
  | nil => simp [h] at hmem
  | cons z zs =>
    have hz : z = x := hall z (by simp [h])
    simp [hz]

theorem root_zero (n : ℕ) (hn : 0 < n) : root basis embedding n 0 = 0 := by
  have hall (z : K) (hz : z ∈ positiveRoots basis embedding n 0) : z = 0 := by
    have he := ((mem_positiveRoots_iff basis embedding n hn z 0).mp hz).1
    exact (pow_eq_zero he)
  unfold root
  cases h : positiveRoots basis embedding n 0 with
  | nil => rfl
  | cons z zs =>
    have hz : z = 0 := hall z (by simp [h])
    simp [hz]

theorem root_pow_of_nonnegative (n : ℕ) (hn : 0 < n) (x : K) (hx : 0 ≤ embedding x) :
    root basis embedding n (x^n) = x := by
  rcases hx.eq_or_lt with hx | hx
  · have he : x = 0 := embedding.injective (by simpa using hx.symm)
    subst x
    simpa [zero_pow hn.ne'] using root_zero basis embedding n hn
  · exact root_pow basis embedding n hn x hx

theorem fp_positiveRoots_of_sign
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x)))
    (n : ℕ) : FP (numberFieldEncoding basis) (numberFieldEncoding basis).list
      (positiveRoots basis embedding n) := by
  exact (fp_roots basis n).comp
    (ListFilterMachines.fp_filter (numberFieldEncoding basis) _ hpos)

theorem fp_root_of_sign
    (hpos : FP (numberFieldEncoding basis) BitEncoding.bool (fun x => decide (0 < embedding x)))
    (n : ℕ) : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
      (root basis embedding n) := by
  exact (fp_positiveRoots_of_sign basis embedding hpos n).comp
    (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)

/-- Root filtering uses the unconditional compiled fixed-field sign machine. -/
theorem fp_positiveRoots (n : ℕ) :
    FP (numberFieldEncoding basis) (numberFieldEncoding basis).list
      (positiveRoots basis embedding n) :=
  fp_positiveRoots_of_sign basis embedding (FixedRealFieldSign.fp_positive basis embedding) n

/-- Ordinary exact polynomial-time recovery of the unique nonnegative root,
with zero as the total default outside the positive-root image. -/
theorem fp_root (n : ℕ) : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
    (root basis embedding n) :=
  fp_root_of_sign basis embedding (FixedRealFieldSign.fp_positive basis embedding) n

end PlanarHom.PositiveFieldPowerRootMachines
