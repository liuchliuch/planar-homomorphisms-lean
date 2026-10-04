import PlanarHom.PlanarTransport

/-! Deleting vertices or edge occurrences preserves ordinary plane drawings. -/
noncomputable section
namespace PlanarHom.MultiGraph

structure IncidenceEmbedding {V E W F : Type*} (G : MultiGraph V E) (H : MultiGraph W F) where
  vertex : V ↪ W
  edge : E ↪ F
  src_eq : ∀ e, H.src (edge e) = vertex (G.src e)
  dst_eq : ∀ e, H.dst (edge e) = vertex (G.dst e)

variable {V E W F : Type*} {G : MultiGraph V E} {H : MultiGraph W F}

def PlaneDrawing.pullback (d : PlaneDrawing H) (i : IncidenceEmbedding G H) : PlaneDrawing G where
  point v := d.point (i.vertex v)
  point_injective := d.point_injective.comp i.vertex.injective
  curve e := d.curve (i.edge e)
  curve_zero e := by rw [d.curve_zero,i.src_eq]
  curve_one e := by rw [d.curve_one,i.dst_eq]
  interior_injective e f s t hs ht h := by
    obtain ⟨hef,hst⟩ := d.interior_injective _ _ s t hs ht h
    exact ⟨i.edge.injective hef,hst⟩
  interior_avoids e t ht v := d.interior_avoids _ t ht _

theorem IncidenceEmbedding.planar (i : IncidenceEmbedding G H) (hH : H.Planar) : G.Planar :=
  hH.map (fun d => d.pullback i)

end PlanarHom.MultiGraph
