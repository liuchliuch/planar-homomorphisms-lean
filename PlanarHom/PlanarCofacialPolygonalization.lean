import PlanarHom.PlanarCofacialAugmentation
import PlanarHom.PlanarExternalArcFaces

/-!
# Polygonal redrawing preserving the designated cofacial pair

The original closure-based face incidence first supplies an actual added edge.
Polygonalization of this augmented graph followed by deletion of precisely that
occurrence certifies cofaciality in the resulting polygonal drawing. No
face-preservation property of arbitrary redrawing is assumed.
-/

noncomputable section
namespace PlanarHom.MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

/-- A designated pair cofacial in an ordinary finite drawing remains cofacial
in some actual polygonal drawing of the same multigraph. -/
theorem PlaneDrawing.Cofacial.exists_cofacialPolygonalDrawing [Finite V] [Finite E]
    {d : PlaneDrawing G} {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) :
    ∃ p : PolygonalDrawing G, p.drawing.Cofacial u v := by
  obtain ⟨p⟩ := hface.exists_withEdge_polygonalDrawing huv
  exact ⟨p.withoutAddedEdge,p.withoutAddedEdge_cofacial⟩

/-- The designated-pair cofacial embedding condition is equivalent to ordinary
planarity after adding one terminal occurrence. Both sides quantify actual
drawings and retain the original finite multigraph incidence. -/
theorem exists_cofacialDrawing_iff_withEdge_planar [Finite V] [Finite E]
    (u v : V) (huv : u ≠ v) :
    (∃ d : PlaneDrawing G, d.Cofacial u v) ↔ (G.withEdge u v).Planar := by
  constructor
  · rintro ⟨d,h⟩
    exact h.withEdge_planar huv
  · rintro ⟨d⟩
    exact ⟨d.withoutAddedEdge,d.withoutAddedEdge_cofacial⟩

/-- Requiring polygonal rather than arbitrary continuous witnesses does not
change the designated-pair cofacial embedding condition. -/
theorem exists_cofacialDrawing_iff_polygonal [Finite V] [Finite E]
    (u v : V) (huv : u ≠ v) :
    (∃ d : PlaneDrawing G, d.Cofacial u v) ↔
      ∃ p : PolygonalDrawing G, p.drawing.Cofacial u v := by
  constructor
  · rintro ⟨d,h⟩
    exact h.exists_cofacialPolygonalDrawing huv
  · rintro ⟨p,hp⟩
    exact ⟨p.drawing,hp⟩

end PlanarHom.MultiGraph
