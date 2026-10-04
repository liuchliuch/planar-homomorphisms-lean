import PlanarHom.SurfaceBooleanGauss

/-! NEW finite Fourier calibration for arbitrary homology-sector signs.
The reconstruction uses all 2^d character twists and coefficients obtained from
an actual sign table. It does not require an Arf or quadratic normal form. -/
namespace PlanarHom.SurfaceBooleanGauss
open scoped BigOperators
variable {K : Type*} [CommRing K]

def walsh {d : ℕ} (f : Bits d→K) (u : Bits d) : K :=
  ∑x : Bits d,character u x*f x

def twistedSectorSum {d : ℕ} (calibration weights : Bits d→K) (u : Bits d) : K :=
  ∑x : Bits d,character u x*calibration x*weights x

theorem walsh_involution {d : ℕ} (f : Bits d→K) (x : Bits d) :
    walsh (walsh f) x=(2:K)^d*f x := by
  classical
  unfold walsh
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑y : Bits d,(∑u : Bits d,character x u*character y u)*f y := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro u _
      rw [character_symm u y]
    _ = ∑y : Bits d,(if x=y then (2:K)^d else 0)*f y := by
      simp only [character_orthogonality]
    _ = (2:K)^d*f x := by simp

/-- Every sign table, calibrated from representatives, yields an exact finite
character reconstruction. No unproved property of Pfaffian signs is assumed. -/
theorem calibrated_reconstruction {d : ℕ} (calibration weights : Bits d→K)
    (hcal : ∀x,calibration x*calibration x=1) :
    (∑u : Bits d,walsh calibration u*twistedSectorSum calibration weights u)=
      (2:K)^d*(∑x : Bits d,weights x) := by
  classical
  unfold twistedSectorSum
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑x : Bits d,(∑u : Bits d,character x u*walsh calibration u)*(calibration x*weights x) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro u _
      rw [character_symm u x]
      ring
    _ = ∑x : Bits d,((2:K)^d*calibration x)*(calibration x*weights x) := by
      change (∑x : Bits d,walsh (walsh calibration) x*(calibration x*weights x))=_
      simp only [walsh_involution]
    _ = (2:K)^d*(∑x : Bits d,weights x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      calc
        _ = (2:K)^d*(calibration x*calibration x)*weights x := by ring
        _ = _ := by rw [hcal x,mul_one]

theorem normalized_calibrated_reconstruction {L : Type*} [Field L] [CharZero L]
    {d : ℕ} (calibration weights : Bits d→L) (hcal : ∀x,calibration x*calibration x=1) :
    (∑x : Bits d,weights x)=((2:L)^d)⁻¹*
      (∑u : Bits d,walsh calibration u*twistedSectorSum calibration weights u) := by
  rw [calibrated_reconstruction calibration weights hcal,←mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:L)≠0)),one_mul]

theorem card_genus_characters (h : ℕ) : Fintype.card (Bits (2*h))=4^h := by
  simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,pow_mul]
  norm_num

end PlanarHom.SurfaceBooleanGauss
