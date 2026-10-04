import PlanarHom.SurfaceMatchingSignInvariance
import PlanarHom.SurfaceQuotientCoordinates
import PlanarHom.SurfaceF2Characters

/-! NEW calibration from actual representative matchings. Equality of their
signs with each homology sector is proved from full class invariance. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates
open MultiGraph MultiGraph.Kasteleyn SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {d : ℕ} (D : R.QuotientCoordinates d)

def matchingCoordinate (M₀ M : Finset E) : Bits d := toBits (D.encode (edgeIndicator (symmDiff M M₀)))

structure MatchingRepresentatives (M₀ : Finset E) (h₀ : G.PerfectMatching M₀) where
  matching : Bits d→Finset E
  perfect : ∀x,G.PerfectMatching (matching x)
  class_eq : ∀x,R.matchingHomologyClass M₀ h₀ (matching x) (perfect x)=R.homologyClass (D.lift (ofBits x))

namespace MatchingRepresentatives
variable {D} {M₀ : Finset E} {h₀ : G.PerfectMatching M₀}
variable (S : D.MatchingRepresentatives M₀ h₀)

def calibration {K : Type*} [CommRing K] (orientation : E→Bool) (x : Bits d) : K :=
  G.matchingPfaffianSign orientation (S.matching x)

theorem calibration_mul_self {K : Type*} [CommRing K] (orientation : E→Bool) (x : Bits d) :
    S.calibration (K:=K) orientation x*S.calibration orientation x=1 := by
  simpa only [calibration,pow_two] using G.matchingPfaffianSign_sq (R:=K) orientation (S.matching x)

theorem matching_class_coordinate {M : Finset E} (hM : G.PerfectMatching M) :
    R.matchingHomologyClass M₀ h₀ (S.matching (D.matchingCoordinate M₀ M)) (S.perfect _)=
      R.matchingHomologyClass M₀ h₀ M hM := by
  rw [S.class_eq,matchingCoordinate,ofBits_toBits]
  exact D.lift_encode_class (R.evenSubgraphCycle _ (hM.symmDiff_even h₀))

theorem calibration_correct {K : Type*} [CommRing K]
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M : Finset E} (hM : G.PerfectMatching M) :
    G.matchingPfaffianSign (R:=K) orientation M=S.calibration orientation (D.matchingCoordinate M₀ M) := by
  have hh:=R.matchingPfaffianSign_eq_of_homology root orientation hfaces hM (S.perfect _) h₀
    (S.matching_class_coordinate hM).symm
  have hc:=congrArg (fun z : ℤ=>(z:K)) hh
  simpa only [G.matchingPfaffianSign_intCast] using hc

end MatchingRepresentatives
end PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates
