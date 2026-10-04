import PlanarHom.SurfaceFisherMaskRepresentatives
import PlanarHom.SurfaceGlobalCalibration

/-! NEW calibration representatives from the literal numeric mask and a
proved realization of the computed quotient lift. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows MultiGraph PlanarityLRRealization SurfaceBooleanGauss
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
variable (R : RotationRows (g.toMultiGraph hg)) {d : ℕ}
variable (D : (FisherInheritedRowCode.typedCubicRows g hg hc R).QuotientCoordinates d)

def maskRepresentatives (liftRows : Bits d→Row)
    (hlift : ∀x,finiteValue (FisherCubicCode.code g).edges.length (liftRows x)=
      (D.lift (ofBits x)).val) :
    D.MatchingRepresentatives (maskMatching g []) (maskMatching_reference_perfect g hg hc) where
  matching x:=maskMatching g (liftRows x)
  perfect x:=maskMatching_perfect g hg hc R (liftRows x) (D.lift (ofBits x)) (hlift x)
  class_eq x:=maskMatching_homology g hg hc R (liftRows x) (D.lift (ofBits x)) (hlift x)

end PlanarHom.SurfaceFisherMatching
