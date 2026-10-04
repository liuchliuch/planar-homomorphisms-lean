import PlanarHom.SurfaceFKTMatchingCorrectness
import PlanarHom.SurfaceFisherMaskCalibration
import PlanarHom.SurfaceFisherMatchingLengths
import PlanarHom.SurfaceRuntimeFaceProducts
import PlanarHom.SurfaceFisherGlobalHomology
import PlanarHom.SurfaceFisherIsingIdentity

/-! NEW final correctness of the actual supplied-row Ising evaluator. The
homology bound is a proved property of its supplied rotation; the wrapper for
serialized complementary regions is stated separately. -/
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 2400000
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows SurfaceBooleanGauss MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] [CharZero K] {kdim : ℕ}
variable (basis : Module.Basis (Fin kdim) ℚ K)
variable (ambient : ℕ) (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hrows : PlanarityRowFaceCode.Realizes g hg rows R)
variable (hgenus : Module.finrank (ZMod 2) R.Homology≤2*ambient)

include basis hrows hgenus in
theorem matchingValue_correct (ρ : K) :
    matchingValue ambient (prepare ρ g rows)=
      ∑M:{M:Finset (Fin (SurfaceFisherCode.code g rows).edges.length) //
        ((SurfaceFisherCode.code g rows).toMultiGraph (SurfaceFisherCode.valid g hg rows R hrows)).PerfectMatching M},
        ∏e∈M.val,(SurfaceFisherCode.weights ρ g rows).getD e.val 0 := by
  let H := SurfaceFisherCode.intermediate g rows
  let hH := SurfaceFisherCode.intermediate_valid g hg rows R hrows
  let hc := SurfaceFisherCode.intermediate_cubic g hg rows R hrows
  let RH := SurfaceFisherCode.typedExpansionRows g hg rows R hrows
  let F := SurfaceFisherCode.code g rows
  let hF := SurfaceFisherCode.valid g hg rows R hrows
  let FR := SurfaceFisherCode.inheritedRows g rows
  let RF := SurfaceFisherCode.typedRows g hg rows R hrows
  let hrF := SurfaceFisherCode.inheritedRows_realizes g hg rows R hrows
  let D := SurfaceRawHomology.computedCoordinates F hF FR RF hrF
  let ls := fun x:Bits (SurfaceRawHomology.dimension F FR) => liftQuotient (SurfaceRawHomology.data F FR) (List.ofFn x)
  have hls : ∀x,finiteValue F.edges.length (ls x)=(D.lift (ofBits x)).val := by
    intro x
    simpa only [finiteValue_ofFn] using SurfaceRawHomology.lift_value F hF FR RF hrF (List.ofFn x)
  let S := SurfaceFisherMatching.maskRepresentatives H hH hc RH D ls hls
  let M₀ := SurfaceFisherMatching.maskMatching H []
  let h₀ := SurfaceFisherMatching.maskMatching_reference_perfect H hH hc
  let T := PlanarityRowFaceCode.runtimeFaceRoots F hF FR RF hrF
  have hfaces := PlanarityRowFaceCode.orientationLog_global_face_products F hF FR RF hrF
  have hd : SurfaceRawHomology.dimension F FR≤2*ambient := by
    apply D.dimension_eq.trans_le
    change Module.finrank (ZMod 2) (SurfaceFisherCode.typedRows g hg rows R hrows).Homology≤_
    rw [SurfaceFisherCode.typedRows_homology_finrank g hg rows R hrows]
    exact hgenus
  have href : ∀e:Fin F.edges.length,bitAt (SurfaceFisherMatching.mask H []) e.val=decide (e∈M₀) := by
    intro e
    simp [M₀,SurfaceFisherMatching.maskMatching]
  have hmasks : ∀x:Bits (SurfaceRawHomology.dimension F FR),∀e:Fin F.edges.length,
      bitAt (SurfaceFisherMatching.mask H (liftQuotient (SurfaceRawHomology.data F FR) (List.ofFn x))) e.val=
        decide (e∈S.matching x) := by
    intro x e
    simp [S,ls,SurfaceFisherMatching.maskRepresentatives,SurfaceFisherMatching.maskMatching]
  have hh := matchingValue_correct_of_representatives basis ambient H F hF FR RF hrF
    (PlanarityRowFaceCode.orientationLog F FR) (SurfaceFisherCode.weights ρ g rows)
    M₀ h₀ S T hfaces hd (le_of_eq (SurfaceFisherMatching.mask_length H [])) href hmasks
  exact hh

include basis hrows hgenus in
theorem value_map_partition (φ : K→+*ℝ) (ρ : K) (hρ : 1+φ ρ≠0) :
    φ (value ambient ρ g rows)=(g.toMultiGraph hg).partition (Boolean.W (φ ρ)) (fun _=>1) := by
  have hm := congrArg φ (matchingValue_correct basis ambient g hg rows R hrows hgenus ρ)
  simp only [map_sum,map_prod] at hm
  have hi := SurfaceFisherCode.ising_matching_identity φ g hg rows R hrows ρ hρ
  rw [MultiGraph.perfectMatchingSum_eq_subtype] at hi
  rw [value,map_mul,hm]
  exact hi.symm

def matrix (ρ : K) (i j : Bool) : K := if i=j then 1 else ρ

theorem map_partition (φ : K→+*ℝ) (ρ : K) :
    φ ((g.toMultiGraph hg).partition (matrix ρ) (fun _=>1))=
      (g.toMultiGraph hg).partition (Boolean.W (φ ρ)) (fun _=>1) := by
  simp only [MultiGraph.partition,map_sum,MultiGraph.assignmentWeight,map_mul,map_prod,
    matrix,Boolean.W,apply_ite,map_one]

include basis hrows hgenus in
theorem value_eq_partition (φ : K→+*ℝ) (ρ : K) (hρ : 1+φ ρ≠0) :
    value ambient ρ g rows=(g.toMultiGraph hg).partition (matrix ρ) (fun _=>1) := by
  apply φ.injective
  rw [value_map_partition basis ambient g hg rows R hrows hgenus φ ρ hρ,map_partition g hg φ ρ]

end PlanarHom.SurfaceFKT
