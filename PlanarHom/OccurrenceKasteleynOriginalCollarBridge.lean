import PlanarHom.RadialPottsAssemblyRibbonGerms

/-! NEW unconditional entry point for the original-drawing normal-collar API. -/
noncomputable section
namespace PlanarHom.MultiGraph
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- Finite ordinary planarity supplies genuine polygonal signed-normal collar
data. No normal field, safe width, straight-germ certificate, rotation system,
or solved orientation is added to the input planarity promise. -/
theorem Planar.exists_polygonal_normal_collars (h : G.Planar) :
    ∃ d : PolygonalDrawing G, Nonempty d.TwoSidedStripData := by
  obtain ⟨d⟩ := h.exists_polygonalDrawing
  exact ⟨d.refineSingle,d.exists_refined_twoSidedStripData⟩

end PlanarHom.MultiGraph
