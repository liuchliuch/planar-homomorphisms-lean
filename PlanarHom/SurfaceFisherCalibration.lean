import PlanarHom.SurfaceFisherRepresentatives
import PlanarHom.SurfacePfaffianFourier

/-! NEW complete semantic Fourier calibration for the actual cubic Fisher
decoration. Every coefficient is computed from its explicit representative
matching; no Pfaffian-orientation or quadratic-sign oracle is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization SurfaceBooleanGauss
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))
variable {d : ℕ} (D : (cubicInheritedRows p R).QuotientCoordinates d)

def cubicMatchingRepresentatives :
    D.MatchingRepresentatives referenceMatching (referenceMatching_perfect p) where
  matching x:=cubicCycleRepresentative p R (D.lift (ofBits x))
  perfect x:=cubicCycleRepresentative_perfect p R (D.lift (ofBits x))
  class_eq x:=cubicCycleRepresentative_homology p R (D.lift (ofBits x))

/-- Exactly 2^d literal signed Pfaffians evaluate the matching sum; the
constructed quotient coordinates prove d=2h on a genus-h component. -/
theorem cubicMatchingSum_fourier [LinearOrder (V×Fin 3)]
    {K : Type*} [Field K] [CharZero K]
    (root : Dart (E⊕(V×Fin 3))) (orientation : E⊕(V×Fin 3)→Bool)
    (hfaces : ∀q : (cubicInheritedRows p R).Face,q≠(cubicInheritedRows p R).faceOf root →
      (∏a : {a : Dart (E⊕(V×Fin 3)) // (cubicInheritedRows p R).faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart (E⊕(V×Fin 3)) // (cubicInheritedRows p R).faceOf a=q}+1))
    (w : E⊕(V×Fin 3)→K) :
    (∑M : {M : Finset (E⊕(V×Fin 3)) // (cubicDecoration p).PerfectMatching M},∏e∈M.val,w e)=
      ((2:K)^d)⁻¹*(∑u : Bits d,
        walsh ((cubicMatchingRepresentatives p R D).calibration orientation) u*
          D.twistedPfaffian orientation referenceMatching u w) :=
  D.matchingSum_eq_fourierPfaffians (cubicMatchingRepresentatives p R D) root orientation hfaces w

end PlanarHom.Fisher
