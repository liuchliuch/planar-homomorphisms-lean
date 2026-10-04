import PlanarHom.SurfaceGlobalSignInvariance
import PlanarHom.SurfaceMatchingCalibration

/-! NEW representative calibration for disconnected rotations, with every
actual component root omitted and empty dart types handled internally. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates.MatchingRepresentatives
open MultiGraph MultiGraph.Kasteleyn SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {d : ℕ} {D : R.QuotientCoordinates d}
variable {M₀ : Finset E} {h₀ : G.PerfectMatching M₀} (S : D.MatchingRepresentatives M₀ h₀)

theorem calibration_correct_roots {K : Type*} [CommRing K]
    (T : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,T.root q≠q→
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M : Finset E} (hM : G.PerfectMatching M) :
    G.matchingPfaffianSign (R:=K) orientation M=S.calibration orientation (D.matchingCoordinate M₀ M) := by
  have hh:=R.matchingPfaffianSign_eq_of_homology_roots T orientation hfaces hM (S.perfect _) h₀
    (S.matching_class_coordinate hM).symm
  have hc:=congrArg (fun z : ℤ=>(z:K)) hh
  simpa only [G.matchingPfaffianSign_intCast] using hc

end PlanarHom.PlanarityLRRealization.RotationRows.QuotientCoordinates.MatchingRepresentatives
