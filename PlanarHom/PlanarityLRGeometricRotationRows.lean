import PlanarHom.PlanarityLRContourCycles
import PlanarHom.OccurrenceKasteleynHostFanChart

/-! NEW exact bridge from literal geometric host-fan charts to row permutations.
The row order is the proved chart order of entire closed fans, not a free choice. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn MultiGraph.PolygonalDrawing.TwoSidedStripData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))

/-- Erase only local host proofs from the actual geometric fan order. -/
def geometricRotationRows (charts : ∀ v, HostFanChart F v) : RotationRows G where
  row v := (charts v).dartRow
  nodup v := (charts v).dartRow_nodup
  mem v a := (charts v).mem_dartRow a

@[simp] theorem geometricRotationRows_row (charts : ∀ v, HostFanChart F v) (v : V) :
    (geometricRotationRows F charts).row v = (charts v).dartRow := rfl

@[simp] theorem geometricRotationRows_rotation (charts : ∀ v, HostFanChart F v) (a : Dart E) :
    (geometricRotationRows F charts).rotation a = ((charts (G.dartPair a).1).dartRow).formPerm a := rfl

open Complexity PlanarityLRDirect PlanarityLRRawConstraints

/-- Exact global contour connectedness for the actual geometric chart rows,
with the selected tree supplied by the raw-input DFS algorithm. -/
theorem geometricContour_sameCycle_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {d : PolygonalDrawing (g.toMultiGraph hg)} {D : d.TwoSidedStripData} {positive : Bool}
    {rays : Dart (Fin g.edges.length) → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))
    (charts : ∀ v, HostFanChart F v) (a b : Dart (Fin g.edges.length)) :
    (contourPermutation (geometricRotationRows F charts) (fun e => isTree g e.val)).SameCycle a b ↔
      componentRoot g (dartHost g a)=componentRoot g (dartHost g b) :=
  dfsContourForRows_sameCycle_iff_componentRoot_eq g hg (geometricRotationRows F charts) a b

theorem mem_geometricContourPortWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {d : PolygonalDrawing (g.toMultiGraph hg)} {D : d.TwoSidedStripData} {positive : Bool}
    {rays : Dart (Fin g.edges.length) → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))
    (charts : ∀ v, HostFanChart F v) (a b : Dart (Fin g.edges.length)) :
    b ∈ contourPortWord (geometricRotationRows F charts) (fun e => isTree g e.val) a ↔
      componentRoot g (dartHost g a)=componentRoot g (dartHost g b) ∧ isTree g b.1.val=false :=
  mem_dfsContourForRowsPortWord g hg (geometricRotationRows F charts) a b

end PlanarHom.PlanarityLRRealization
