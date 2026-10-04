import PlanarHom.SurfaceGlobalCalibration
import PlanarHom.SurfacePfaffianFourier
import PlanarHom.SurfaceFisherCalibration

/-! NEW full disconnected weighted Fourier/Pfaffian identity. The actual
component root selector replaces the connected single-face hypothesis. -/
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates
open MultiGraph MultiGraph.Kasteleyn SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {d : ℕ} (D : R.QuotientCoordinates d)
variable {K : Type*} [CommRing K]

theorem twistedPfaffian_eq_matchingSum_roots
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (T : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,T.root q≠q →
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
  rw [prod_twistWeights,S.calibration_correct_roots T orientation hfaces M.property]
  calc
    _ = (characterF2 u (D.encode (edgeIndicator M₀))*characterF2 u (D.encode (edgeIndicator M.val)))*
        S.calibration orientation (D.matchingCoordinate M₀ M.val)*(∏e∈M.val,w e) := by ring
    _ = _ := by rw [D.reference_character_product]

theorem matchingSum_fourier_unnormalized_roots
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (T : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,T.root q≠q →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    (w : E→K) :
    (∑u : Bits d,walsh (S.calibration orientation) u*D.twistedPfaffian orientation M₀ u w)=
      (2:K)^d*(∑M : {M : Finset E // G.PerfectMatching M},∏e∈M.val,w e) := by
  simp_rw [D.twistedPfaffian_eq_matchingSum_roots S T orientation hfaces]
  exact calibrated_indexed_reconstruction (K:=K) (T:={M : Finset E // G.PerfectMatching M}) (d:=d) (fun M=>D.matchingCoordinate M₀ M.val)
    (S.calibration orientation) (fun M=>∏e∈M.val,w e) (S.calibration_mul_self orientation)

/-- The actual field-valued Fourier/Pfaffian identity. Genus bounds limit d;
they are not needed for correctness of this weighted algebraic formula. -/
theorem matchingSum_eq_fourierPfaffians_roots {L : Type*} [Field L] [CharZero L]
    {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)
    (T : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,T.root q≠q →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    (w : E→L) :
    (∑M : {M : Finset E // G.PerfectMatching M},∏e∈M.val,w e)=
      ((2:L)^d)⁻¹*(∑u : Bits d,walsh (S.calibration orientation) u*D.twistedPfaffian orientation M₀ u w) := by
  rw [D.matchingSum_fourier_unnormalized_roots S T orientation hfaces w,←mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:L)≠0)),one_mul]

end PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates

namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))
variable {d : ℕ} (D : (cubicInheritedRows p R).QuotientCoordinates d)

theorem cubicMatchingSum_fourier_roots [LinearOrder (V×Fin 3)]
    {K : Type*} [Field K] [CharZero K]
    (T : (cubicInheritedRows p R).FaceRoots) (orientation : E⊕(V×Fin 3)→Bool)
    (hfaces : ∀q : (cubicInheritedRows p R).Face,T.root q≠q→
      (∏a : {a : Dart (E⊕(V×Fin 3)) // (cubicInheritedRows p R).faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart (E⊕(V×Fin 3)) // (cubicInheritedRows p R).faceOf a=q}+1))
    (w : E⊕(V×Fin 3)→K) :
    (∑M : {M : Finset (E⊕(V×Fin 3)) // (cubicDecoration p).PerfectMatching M},∏e∈M.val,w e)=
      ((2:K)^d)⁻¹*(∑u : Bits d,
        walsh ((cubicMatchingRepresentatives p R D).calibration orientation) u*
          D.twistedPfaffian orientation referenceMatching u w) :=
  D.matchingSum_eq_fourierPfaffians_roots (cubicMatchingRepresentatives p R D) T orientation hfaces w

end PlanarHom.Fisher
