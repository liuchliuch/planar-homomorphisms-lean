import PlanarHom.FixedFieldPowerRootCandidates
import Mathlib.Data.Real.Basic

/-! # Exact odd-power root recovery in a fixed real number field

Odd powers are injective under a real embedding, so the first verified root is
the unique root. This endpoint needs no order-testing machine on field values.
-/

noncomputable section
namespace PlanarHom.FixedFieldOddPowerRootMachines
open Complexity FixedFieldPowerRootCandidates

variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)

def root (n : ℕ) (y : K) : K := (roots basis n y).headD 0

theorem fp_root (n : ℕ) : FP (numberFieldEncoding basis) (numberFieldEncoding basis) (root basis n) :=
  (fp_roots basis n).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)

theorem root_pow (embedding : K →+* ℝ) (n : ℕ) (hn : Odd n) (x : K) :
    root basis n (x^n) = x := by
  have hmem : x ∈ roots basis n (x^n) := (mem_roots_iff basis n hn.pos x (x^n)).mpr rfl
  have hall (z : K) (hz : z ∈ roots basis n (x^n)) : z = x := by
    have he := (mem_roots_iff basis n hn.pos z (x^n)).mp hz
    apply embedding.injective
    apply hn.pow_injective
    simpa only [map_pow] using congrArg embedding he
  unfold root
  cases h : roots basis n (x^n) with
  | nil => simp [h] at hmem
  | cons z zs =>
    have hz : z = x := hall z (by simp [h])
    simp [hz]

end PlanarHom.FixedFieldOddPowerRootMachines
