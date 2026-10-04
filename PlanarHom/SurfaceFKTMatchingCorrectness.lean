import PlanarHom.SurfaceFKTPfaffianSemantics

/-! NEW correctness of the complete list evaluator from the internally
constructed raw coordinates and representative masks. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows SurfaceBooleanGauss MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] [CharZero K] {kdim : ℕ}
variable (basis : Module.Basis (Fin kdim) ℚ K)
variable (ambient : ℕ) (cubic g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hrows : PlanarityRowFaceCode.Realizes g hg rows R) (log : List ℕ) (w : List K)

include basis in
theorem matchingValue_correct_of_representatives
    (M₀ : Finset (Fin g.edges.length)) (h₀ : (g.toMultiGraph hg).PerfectMatching M₀)
    (S : (SurfaceRawHomology.computedCoordinates g hg rows R hrows).MatchingRepresentatives M₀ h₀)
    (T : R.FaceRoots)
    (hfaces : ∀q:R.Face,T.root q≠q →
      (∏a:{a:Dart (Fin g.edges.length) // R.faceOf a=q},dartSign (fun e=>logOrientation log e.val) a.val)=
        (-1:ℤ)^(Fintype.card {a:Dart (Fin g.edges.length) // R.faceOf a=q}+1))
    (hbound : SurfaceRawHomology.dimension g rows≤2*ambient)
    (hlen : (SurfaceFisherMatching.mask cubic []).length≤g.edges.length)
    (href : ∀e:Fin g.edges.length,bitAt (SurfaceFisherMatching.mask cubic []) e.val=decide (e∈M₀))
    (hmask : ∀x:Bits (SurfaceRawHomology.dimension g rows),∀e:Fin g.edges.length,
      bitAt (SurfaceFisherMatching.mask cubic (liftQuotient (SurfaceRawHomology.data g rows) (List.ofFn x))) e.val=
        decide (e∈S.matching x)) :
    matchingValue ambient (preparedOn cubic g rows log w)=
      ∑M:{M:Finset (Fin g.edges.length) // (g.toMultiGraph hg).PerfectMatching M},
        ∏e∈M.val,w.getD e.val 0 := by
  have hcal : (fun x:Bits (SurfaceRawHomology.dimension g rows) =>
      calibration (preparedOn cubic g rows log w) (List.ofFn x))=
      S.calibration (K:=K) (fun e => logOrientation log e.val) := by
    funext x
    exact calibration_eq_sign basis cubic g hg rows log w x (S.matching x) (S.perfect x) (hmask x)
  have htw : (fun u:Bits (SurfaceRawHomology.dimension g rows) =>
      twistedEvaluation (preparedOn cubic g rows log w) (List.ofFn u))=
      fun u => (SurfaceRawHomology.computedCoordinates g hg rows R hrows).twistedPfaffian
        (fun e=>logOrientation log e.val) M₀ u (fun e=>w.getD e.val 0) := by
    funext u
    exact twistedEvaluation_eq basis cubic g hg rows R hrows log w M₀ hlen href u
  rw [matchingValue_eq_fourier ambient (preparedOn cubic g rows log w) hbound]
  change ((2:K)^(SurfaceRawHomology.dimension g rows))⁻¹*
    (∑u:Bits (SurfaceRawHomology.dimension g rows),
      SurfaceBooleanGauss.walsh (fun x => calibration (preparedOn cubic g rows log w) (List.ofFn x)) u *
        (fun u=>twistedEvaluation (preparedOn cubic g rows log w) (List.ofFn u)) u)=_
  rw [hcal,htw]
  exact ((SurfaceRawHomology.computedCoordinates g hg rows R hrows).matchingSum_eq_fourierPfaffians_roots
    S T (fun e=>logOrientation log e.val) hfaces (fun e=>w.getD e.val 0)).symm

end PlanarHom.SurfaceFKT
