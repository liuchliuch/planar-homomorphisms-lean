import PlanarHom.RadialPottsTileLongCoordinates
import PlanarHom.RadialPottsTileShortCoordinates

/-! NEW genuine all-k drawing of the original occurrence-sensitive radial tile.
Every coordinate and every edge is literal; no geometric certificate is assumed. -/
noncomputable section
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing RadialPottsTile RadialPottsTileCoordinates

theorem edge_start {k : ℕ} (e : Edge k) :
    point ((graph k).src e)=(edgeSegment e).start k := by
  cases e with
  | inl e => exact long_start e
  | inr e => exact short_start e

theorem edge_finish {k : ℕ} (e : Edge k) :
    point ((graph k).dst e)=(edgeSegment e).finish := by
  cases e with
  | inl e => exact long_finish e
  | inr e => exact short_finish e

def integerCertificate (k : ℕ) : Certificate (graph k) point where
  injective := RadialPottsTileCoordinates.point_injective
  nondegenerate e := by rw [edge_start,edge_finish]; exact Segment.nondegenerate _ _
  separated e f hne := by
    rw [edge_start,edge_finish,edge_start,edge_finish]
    exact Segment.separated _ _ _ (edgeSegment_valid e) (edgeSegment_valid f)
      (fun he=>hne (edgeSegment_injective he))
  avoids e v := by rw [edge_start,edge_finish]; exact Segment.avoids _ _ _

def unscaledDrawing (k : ℕ) : MultiGraph.PlaneDrawing (graph k) := IntegerStraightDrawing.drawing (integerCertificate k)

theorem planar (k : ℕ) : (graph k).Planar := ⟨unscaledDrawing k⟩

end PlanarHom.RadialPottsTileGeometry
