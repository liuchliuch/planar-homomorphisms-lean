import PlanarHom.SurfaceMatchingCalibration
import PlanarHom.SurfaceIndexedFourier

/-! NEW exact surface matching evaluation by character-twisted Pfaffians.
All calibration values are signs of actual representative matchings; their
validity is derived from face equations and the proved full homology-class
invariance. The identity permits arbitrary signed or zero field weights. -/
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates
open MultiGraph MultiGraph.Kasteleyn SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {d : ℕ} (D : R.QuotientCoordinates d)
variable {K : Type*} [CommRing K]

theorem reference_character_product (M₀ M : Finset E) (u : Bits d) :
    characterF2 (K:=K) u (D.encode (edgeIndicator M₀))*characterF2 u (D.encode (edgeIndicator M))=
      character u (D.matchingCoordinate M₀ M) := by
  change _=characterF2 u (D.encode (edgeIndicator (symmDiff M M₀)))
  rw [edgeIndicator_symmDiff,map_add,characterF2_add,mul_comm]

def twistedPfaffian (orientation : E→Bool) (M₀ : Finset E) (u : Bits d) (w : E→K) : K :=
  characterF2 u (D.encode (edgeIndicator M₀))*
    pairingPfaffian (G.occurrenceSkewMatrix orientation (twistWeights D.encode u w))

theorem twistedPfaffian_eq_matchingSum
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    (u : Bits d) (w : E→K) :
    D.twistedPfaffian orientation M₀ u w=
      ∑M : {M : Finset E // G.PerfectMatching M},
        character u (D.matchingCoordinate M₀ M.val)*S.calibration orientation (D.matchingCoordinate M₀ M.val)*
          (∏e∈M.val,w e) := by
  rw [twistedPfaffian,G.pairingPfaffian_occurrenceSkewMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  rw [prod_twistWeights,S.calibration_correct root orientation hfaces M.property]
  calc
    _ = (characterF2 u (D.encode (edgeIndicator M₀))*characterF2 u (D.encode (edgeIndicator M.val)))*
        S.calibration orientation (D.matchingCoordinate M₀ M.val)*(∏e∈M.val,w e) := by ring
    _ = _ := by rw [D.reference_character_product]

theorem matchingSum_fourier_unnormalized
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    (w : E→K) :
    (∑u : Bits d,walsh (S.calibration orientation) u*D.twistedPfaffian orientation M₀ u w)=
      (2:K)^d*(∑M : {M : Finset E // G.PerfectMatching M},∏e∈M.val,w e) := by
  simp_rw [D.twistedPfaffian_eq_matchingSum S root orientation hfaces]
  exact calibrated_indexed_reconstruction (K:=K) (T:={M : Finset E // G.PerfectMatching M}) (d:=d) (fun M=>D.matchingCoordinate M₀ M.val)
    (S.calibration orientation) (fun M=>∏e∈M.val,w e) (S.calibration_mul_self orientation)

/-- The actual field-valued Fourier/Pfaffian identity. Genus bounds limit d;
they are not needed for correctness of this weighted algebraic formula. -/
theorem matchingSum_eq_fourierPfaffians {L : Type*} [Field L] [CharZero L]
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    (w : E→L) :
    (∑M : {M : Finset E // G.PerfectMatching M},∏e∈M.val,w e)=
      ((2:L)^d)⁻¹*(∑u : Bits d,walsh (S.calibration orientation) u*D.twistedPfaffian orientation M₀ u w) := by
  rw [D.matchingSum_fourier_unnormalized S root orientation hfaces w,←mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:L)≠0)),one_mul]

end PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates
