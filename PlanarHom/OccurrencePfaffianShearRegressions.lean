import PlanarHom.OccurrencePfaffianShear
import PlanarHom.OccurrencePfaffianCoreRegressions
import Mathlib.Data.ZMod.Basic

/-! NEW regression proofs for the literal pairing shear theorem. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.ReconstructedPfaffianShearRegression

/-- The two-dimensional off-diagonal value survives an arbitrary shear. -/
theorem two_vertex_shear (x c : ℤ) :
    pairingPfaffian (fun u v : Fin 2 =>
      (![![0,x],![-x,0]] : Matrix (Fin 2) (Fin 2) ℤ) u v +
      (if u = 1 then c * (![![0,x],![-x,0]] : Matrix (Fin 2) (Fin 2) ℤ) 0 v else 0) +
      (if v = 1 then c * (![![0,x],![-x,0]] : Matrix (Fin 2) (Fin 2) ℤ) u 0 else 0)) = x := by
  rw [← supportedPfaffian_univ, supportedPfaffian_elementaryShear _ _ 0 1 c
    (by simp) (by simp) (by decide)]
  · rw [supportedPfaffian_univ,pairingPfaffian_fin_two]
    rfl
  · intro u v
    fin_cases u <;> fin_cases v <;> simp
  · intro u
    fin_cases u <;> rfl

/-- A characteristic-two regression ensures cancellation never divides by two. -/
theorem characteristic_two_shear (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    pairingPfaffian (fun u v => A u v + (if u = 3 then A 1 v else 0) +
      (if v = 3 then A u 1 else 0)) = pairingPfaffian A := by
  have h := supportedPfaffian_elementaryShear Finset.univ A 1 3 1
    (by simp) (by simp) (by decide) hskew hdiag
  simpa only [supportedPfaffian_univ,one_mul] using h

/-- Inactive ambient vertices do not affect a supported shear. -/
theorem nonconsecutive_active_shear (A : Matrix (Fin 5) (Fin 5) ℚ) (c : ℚ)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    supportedPfaffian {1,4} (fun u v => A u v +
      (if u = 4 then c * A 1 v else 0) + (if v = 4 then c * A u 1 else 0)) = A 1 4 := by
  rw [supportedPfaffian_elementaryShear _ A 1 4 c (by simp) (by simp) (by decide) hskew hdiag]
  exact ReconstructedPfaffianCoreRegression.supported_pair 1 4 (by decide) A

/-- Repeated rows vanish without positivity, genericity, or nonzero entries. -/
theorem signed_repeated_rows :
    pairingPfaffian (![![(0 : ℤ),0,2,3], ![0,0,2,3], ![-2,-2,0,-5], ![-3,-3,5,0]]) = 0 := by
  rw [← supportedPfaffian_univ]
  apply supportedPfaffian_eq_zero_of_equal_rows _ _ 0 1 (by simp) (by simp) (by decide)
  · intro u v
    fin_cases u <;> fin_cases v <;> norm_num
  · intro u
    fin_cases u <;> rfl
  · intro v
    rfl

end PlanarHom.MultiGraph.ReconstructedPfaffianShearRegression
