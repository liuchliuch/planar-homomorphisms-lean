import PlanarHom.PlanarityLRGeometricContourIdentification
import PlanarHom.PlanarityLRComputedRootCircleRouting

/-! NEW ordinary-input necessity: actual computed DFS contours of a single
geometric row system have no alternating occurrence pairs. The proof constructs
all paths and identifies their literal recursive words before using crossing. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch
open MultiGraph.PolygonalDrawing.TwoSidedStripData
open MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

def RootPortsNonalternating (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) : Prop :=
  ∀ r : Fin g.vertices, height g r.val=0 → ∀ a b : Dart (Fin g.edges.length), a.1≠b.1 →
    ¬ [a,b,(a.1,!a.2),(b.1,!b.2)].Sublist (directedRootPorts g hg rows r)

/-- Ordinary planarity supplies a common row family whose actual DFS contour
port words are nonalternating, including loops and parallel occurrences. -/
theorem planar_exists_nonalternating_rows (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    ∃ rows : RotationRows (dfsGraph g hp.1), RootPortsNonalternating g hp.1 rows := by
  obtain ⟨d,D,rays,_,F,C,charts,hroute⟩ := exists_computedRootCircleRoutings g hp false
  refine ⟨dfsGeometricRows g hp.1 F charts,?_⟩
  intro r hr a b hab
  obtain ⟨R⟩ := hroute r
  have hw := computedComponentRootWord_eq g hp.1 F charts r R.word
  have he : (⟨componentRoot g r.val,(componentRoot_spec g r.isLt).1⟩ : Fin g.vertices)=r :=
    Fin.ext (componentRoot_eq_self g r.isLt hr)
  rw [he] at hw
  rw [←hw]
  exact R.no_alternating_label_sublist a b hab

end PlanarHom.PlanarityLRRealization
