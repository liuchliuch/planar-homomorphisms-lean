import PlanarHom.CubeGraphMetric
import PlanarHom.CubeBCHRigidity
import PlanarHom.LogarithmicSupport

/-!
# Concrete cube squares and positive uniform direction matrices
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.Boolean

/-- Flipping one coordinate is an actual Cartesian cube edge. -/
theorem cubeGraph_adj_flip {d : ℕ} (z : Cube d) (r : Fin d) :
    (cubeGraph d).Adj z (flip z r) :=
  (hammingGraph_adj_iff_flip z (flip z r)).mpr ⟨r, rfl⟩

/-- Two distinct flips have actual graph distance two. -/
theorem cubeGraph_dist_two_flips {d : ℕ} (z : Cube d) (r s : Fin d) (hrs : r ≠ s) :
    (cubeGraph d).dist z (flip (flip z r) s) = 2 := by
  rw [cubeGraph_dist]
  have hterm (k : Fin d) :
      (if z k = flip (flip z r) s k then (0 : ℕ) else 1) =
        (if k = r then 1 else 0) + (if k = s then 1 else 0) := by
    by_cases hkr : k = r
    · subst k
      have he : flip (flip z r) s r = !(z r) := by
        rw [flip_apply_ne _ s r hrs, flip_apply_same]
      cases hz : z r <;> simp [he, hz, hrs]
    · by_cases hks : k = s
      · subst k
        have he : flip (flip z r) s s = !(z s) := by
          rw [flip_apply_same, flip_apply_ne z r s (Ne.symm hrs)]
        cases hz : z s <;> simp [he, hz, Ne.symm hrs]
      · simp only [flip_apply_ne _ s k hks, flip_apply_ne z r k hkr,
          hkr, hks, ite_false, ite_true, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib]
  simp

/-- The other diagonal of the same concrete cube square also has distance two. -/
theorem cubeGraph_dist_distinct_flips {d : ℕ} (z : Cube d) (r s : Fin d) (hrs : r ≠ s) :
    (cubeGraph d).dist (flip z r) (flip z s) = 2 := by
  simpa only [flip_flip] using cubeGraph_dist_two_flips (flip z r) r s hrs

/-- A uniform coordinate direction operator in the fixed Boolean coordinates. -/
def uniformDirectionMatrix (d : ℕ) (c b : ℝ) : Matrix (Cube d) (Cube d) ℝ :=
  c • 1 + ∑ r : Fin d, b • bitFlipMatrix r

theorem uniformDirectionMatrix_isHermitian (d : ℕ) (c b : ℝ) :
    (uniformDirectionMatrix d c b).IsHermitian := scalar_add_directions_isHermitian c (fun _ => b)

/-- Each cube edge entry is literally the uniform coefficient. -/
theorem uniformDirectionMatrix_flip {d : ℕ} (c b : ℝ) (z : Cube d) (r : Fin d) :
    uniformDirectionMatrix d c b z (flip z r) = b := by
  have hn : z ≠ flip z r := Ne.symm (flip_ne_self z r)
  simp [uniformDirectionMatrix, Matrix.sum_apply, bitFlipMatrix_flip, hn]

/-- A nonzero uniform coefficient gives exactly the genuine cube graph as support. -/
theorem uniformDirectionMatrix_support {d : ℕ} (c b : ℝ) (hb : b ≠ 0) :
    LogarithmicSupport.offDiagonalSupport (uniformDirectionMatrix d c b)
      (uniformDirectionMatrix_isHermitian d c b) = cubeGraph d := by
  ext z w
  rw [LogarithmicSupport.offDiagonalSupport_adj]
  change (_ ∧ _) ↔ (CartesianGeometry.hammingGraph (fun _ : Fin d => Bool)).Adj z w
  rw [hammingGraph_adj_iff_flip]
  constructor
  · rintro ⟨hzw, hne⟩
    by_contra hn
    have hnone : ∀ r, w ≠ flip z r := not_exists.mp hn
    exact hne (scalar_add_directions_nonedge c (fun _ => b) z w hzw hnone)
  · rintro ⟨r, rfl⟩
    exact ⟨Ne.symm (flip_ne_self z r), by simpa only [uniformDirectionMatrix_flip] using hb⟩

/-- Positive uniform coefficients are positive on every cube edge. -/
theorem uniformDirectionMatrix_edge_pos {d : ℕ} (c b : ℝ) (hb : 0 < b)
    (z w : Cube d) (h : (cubeGraph d).Adj z w) :
    0 < uniformDirectionMatrix d c b z w := by
  obtain ⟨r, rfl⟩ := (hammingGraph_adj_iff_flip z w).mp h
  simpa only [uniformDirectionMatrix_flip] using hb

end PlanarHom.Boolean
