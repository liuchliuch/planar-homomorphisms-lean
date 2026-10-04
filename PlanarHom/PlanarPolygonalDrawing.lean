import PlanarHom.PolygonalArc

/-!
# Ordinary plane drawings with explicit finite polygonal edge data

The geometric conditions remain those of an ordinary plane drawing. In
particular this permits loops, whose two endpoint parameters coincide, without
imposing injectivity on the entire closed interval. Every edge curve is the
actual strict parametrization of a finite chain of straight segments.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph

/-- A finite polygonal refinement of an ordinary plane drawing. This is
geometric output data; it does not alter the abstract graph input promise. -/
structure PolygonalDrawing {V E : Type*} (G : MultiGraph V E) where
  drawing : PlaneDrawing G
  chain : ∀ e : E, Polygonal.Chain Set.univ (drawing.point (G.src e)) (drawing.point (G.dst e))
  curve_eq : ∀ e, drawing.curve e = (chain e).strictPath.toContinuousMap

namespace PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Polygonal drawing data yields the original ordinary planarity predicate. -/
theorem planar (d : PolygonalDrawing G) : G.Planar := ⟨d.drawing⟩

/-- The finite segment-chain support is exactly the original drawn edge. -/
theorem chain_support_eq_curve_range (d : PolygonalDrawing G) (e : E) :
    (d.chain e).support = Set.range (d.drawing.curve e) := by
  rw [← Polygonal.Chain.range_strictPath, d.curve_eq]
  rfl

/-- All polygonal pieces retain their original place in the drawn graph. -/
theorem chain_support_subset_drawing (d : PolygonalDrawing G) (e : E) :
    (d.chain e).support ⊆ d.drawing.support := by
  rw [d.chain_support_eq_curve_range e]
  intro p hp
  exact Or.inr (Set.mem_iUnion.mpr ⟨e, hp⟩)

end PolygonalDrawing
end PlanarHom.MultiGraph
