import PlanarHom.SchurExponentialLog
import PlanarHom.LogarithmicSupport

/-!
# Graph-distance leading coefficient of the genuine matrix exponential

The first nonzero coefficient is derived from support-graph distance and
positive shortest-path products. Arbitrary signed diagonal entries are allowed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The source expansion in Lemma 4.2, with its actual shortest-distance coefficient. -/
theorem exp_entry_distance_leading_isBigO (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (i j : V) :
    let d := (LogarithmicSupport.offDiagonalSupport L hL).dist i j
    (fun t : ℝ => NormedSpace.exp ℝ (t • L) i j -
      ((L ^ d) i j / (d.factorial : ℝ)) * t ^ d) =O[𝓝 0]
      (fun t : ℝ => t ^ (d + 1)) := by
  let d := (LogarithmicSupport.offDiagonalSupport L hL).dist i j
  have hpoly : ∀ t, expTaylor L (d + 1) t i j =
      ((L ^ d) i j / (d.factorial : ℝ)) * t ^ d := by
    intro t
    simp only [expTaylor, Finset.sum_range_succ,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hz : ∑ k ∈ Finset.range d, (t ^ k / (k.factorial : ℝ)) * (L ^ k) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hzero := LogarithmicSupport.pow_entry_eq_zero_of_lt_dist L hL
        (i := i) (j := j) (Finset.mem_range.mp hk)
      rw [hzero, mul_zero]
    rw [hz, zero_add]
    ring
  have h := entry_isBigO (exp_sub_expTaylor_isBigO L (d + 1)) i j
  simpa only [Matrix.sub_apply, hpoly] using h

/-- With connected positive logarithmic edge support, the leading coefficient
is strictly positive, including diagonal indices and distance zero. -/
theorem exp_distance_leading_coefficient_pos (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hconn : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (i j : V) :
    let d := (LogarithmicSupport.offDiagonalSupport L hL).dist i j
    0 < (L ^ d) i j / (d.factorial : ℝ) := by
  apply div_pos
  · exact LogarithmicSupport.pow_distance_entry_pos L hL hconn hedge i j
  · exact_mod_cast Nat.factorial_pos _

end PlanarHom.MatrixLogCoefficients
