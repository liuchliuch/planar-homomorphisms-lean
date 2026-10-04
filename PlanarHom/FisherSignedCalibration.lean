import PlanarHom.FisherCubicCodeSignSemantics
import PlanarHom.OccurrenceSkewCodeSemantics

/-! NEW exact numeric calibration with the explicit reference matching. The
orientation premise is supplied by the separately proved inherited-row compiler. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph MultiGraph.Kasteleyn
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

 theorem calibrated_evaluation (basis : Module.Basis (Fin dimension) ℚ K) (φ : K→+*ℝ)
    {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3) (log : List ℕ)
    (ho : ((code g).toMultiGraph (valid g hg hc)).IsPfaffianOrientation (fun e=>logOrientation log e.val))
    (x : List K) :
    φ (referenceSign g log*PfaffianList.evaluateGrid (OccurrenceSkewCode.grid (code g,(log,weights g x))))=
      ((code g).toMultiGraph (valid g hg hc)).perfectMatchingSum (fun e=>φ ((weights g x).getD e.val 0)) := by
  have hh:=OccurrenceSkewCode.calibrated_evaluation basis (code g,(log,weights g x))
    (valid g hg hc) ho (referenceMatching g hg hc) (referenceMatching_perfect g hg hc)
  rw [←referenceSign_eq g hg hc log] at hh
  have hmap:=congrArg φ hh
  rw [MultiGraph.perfectMatchingSum_eq_subtype]
  simpa only [map_sum,map_prod] using hmap.symm

end PlanarHom.FisherCubicCode
