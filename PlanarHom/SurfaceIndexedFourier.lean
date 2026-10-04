import PlanarHom.SurfaceFourierCalibration

/-! NEW character inversion on an arbitrary finite family carrying quotient
coordinates. Multiple objects in one class are retained with their weights. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceBooleanGauss
variable {K T : Type*} [CommRing K] [Fintype T] {d : ℕ}

theorem calibrated_indexed_reconstruction (coordinate : T→Bits d)
    (calibration : Bits d→K) (weights : T→K)
    (hcal : ∀x,calibration x*calibration x=1) :
    (∑u : Bits d,walsh calibration u*
      (∑a : T,character u (coordinate a)*calibration (coordinate a)*weights a))=
      (2:K)^d*(∑a : T,weights a) := by
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑a : T,(∑u : Bits d,character (coordinate a) u*walsh calibration u)*
        (calibration (coordinate a)*weights a) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro u _
      rw [character_symm u (coordinate a)]
      ring
    _ = ∑a : T,((2:K)^d*calibration (coordinate a))*(calibration (coordinate a)*weights a) := by
      change (∑a : T,walsh (walsh calibration) (coordinate a)*(calibration (coordinate a)*weights a))=_
      simp only [walsh_involution]
    _ = (2:K)^d*(∑a : T,weights a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = (2:K)^d*(calibration (coordinate a)*calibration (coordinate a))*weights a := by ring
        _ = _ := by rw [hcal,mul_one]

end PlanarHom.SurfaceBooleanGauss
