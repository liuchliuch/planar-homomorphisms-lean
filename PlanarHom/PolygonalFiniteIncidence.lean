import PlanarHom.PolygonalHostFree

/-!
# The actual finite piece and host sets of a polygonal drawing

The finsets here are extracted from finite edge chains. They are proof-level
geometric data and are not substituted for the ordinary serialized graph input.
-/

noncomputable section
open Set
namespace PlanarHom.MultiGraph.PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

theorem finite_segmentSet [Finite E] (d : PolygonalDrawing G) : d.segmentSet.Finite := by
  have h := Set.finite_iUnion (fun e : E => (d.chain e).segments.finite_toSet)
  convert h using 1
  ext p
  simp only [segmentSet,Set.mem_setOf_eq,Set.mem_iUnion]

def segmentFinset [Finite E] (d : PolygonalDrawing G) : Finset (Plane × Plane) :=
  d.finite_segmentSet.toFinset

@[simp] theorem mem_segmentFinset [Finite E] (d : PolygonalDrawing G) (p : Plane × Plane) :
    p ∈ d.segmentFinset ↔ p ∈ d.segmentSet := by simp [segmentFinset]

@[simp] theorem coe_segmentFinset [Finite E] (d : PolygonalDrawing G) :
    (d.segmentFinset : Set (Plane × Plane)) = d.segmentSet := by ext p; simp

theorem finite_hostSet [Finite V] (d : PolygonalDrawing G) : d.hostSet.Finite :=
  Set.finite_range d.drawing.point

theorem chain_segment_mem_finset [Finite E] (d : PolygonalDrawing G) (e : E)
    {p : Plane × Plane} (hp : p ∈ (d.chain e).segments) : p ∈ d.segmentFinset :=
  (d.mem_segmentFinset p).mpr ⟨e,hp⟩

end PlanarHom.MultiGraph.PolygonalDrawing
