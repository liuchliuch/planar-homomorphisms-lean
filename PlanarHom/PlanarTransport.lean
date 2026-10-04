import PlanarHom.PlanarEmbedding

/-!
# Incidence reindexing and geometric planarity transport

The bijections below preserve every vertex and every edge occurrence. Loops,
parallel edges, disconnected graphs and isolated vertices need no exceptions.
Drawings are transported using the inverse label bijections; their actual subset
of the plane is unchanged. No algorithm for recognizing planarity is asserted.
-/

noncomputable section
namespace PlanarHom.MultiGraph

/-- Orientation-preserving relabeling of an incidence presentation. This is more
specific than an undirected-graph isomorphism, since endpoint order is preserved. -/
structure IncidenceEquiv {V E W F : Type*} (G : MultiGraph V E) (H : MultiGraph W F) where
  vertex : V ≃ W
  edge : E ≃ F
  src_eq : ∀ e, H.src (edge e) = vertex (G.src e)
  dst_eq : ∀ e, H.dst (edge e) = vertex (G.dst e)

namespace IncidenceEquiv
variable {V E W F X A : Type*} {G : MultiGraph V E} {H : MultiGraph W F}
  {K : MultiGraph X A}

/-- Reverse both label bijections. -/
def symm (i : IncidenceEquiv G H) : IncidenceEquiv H G where
  vertex := i.vertex.symm
  edge := i.edge.symm
  src_eq f := by
    apply i.vertex.injective
    simpa using (i.src_eq (i.edge.symm f)).symm
  dst_eq f := by
    apply i.vertex.injective
    simpa using (i.dst_eq (i.edge.symm f)).symm

/-- Compose actual incidence relabelings. -/
def trans (i : IncidenceEquiv G H) (j : IncidenceEquiv H K) : IncidenceEquiv G K where
  vertex := i.vertex.trans j.vertex
  edge := i.edge.trans j.edge
  src_eq e := by simp only [Equiv.trans_apply, j.src_eq, i.src_eq]
  dst_eq e := by simp only [Equiv.trans_apply, j.dst_eq, i.dst_eq]

end IncidenceEquiv

/-- Reindex both finite labels without changing graph incidence. -/
def reindex {V E W F : Type*} (G : MultiGraph V E) (v : V ≃ W) (e : E ≃ F) :
    MultiGraph W F where
  src f := v (G.src (e.symm f))
  dst f := v (G.dst (e.symm f))

/-- The reindexed presentation is incidence-equivalent to the old one. -/
def reindexEquiv {V E W F : Type*} (G : MultiGraph V E) (v : V ≃ W) (e : E ≃ F) :
    IncidenceEquiv G (G.reindex v e) where
  vertex := v
  edge := e
  src_eq x := by simp [reindex]
  dst_eq x := by simp [reindex]

namespace PlaneDrawing
variable {V E W F : Type*} {G : MultiGraph V E} {H : MultiGraph W F}

/-- Transport actual plane coordinates and curves through both inverse label
bijections. No drawing is chosen or computed by this operation. -/
def transport (d : PlaneDrawing G) (i : IncidenceEquiv G H) : PlaneDrawing H where
  point w := d.point (i.vertex.symm w)
  point_injective := d.point_injective.comp i.vertex.symm.injective
  curve f := d.curve (i.edge.symm f)
  curve_zero f := by
    rw [d.curve_zero]
    exact congrArg d.point (i.symm.src_eq f)
  curve_one f := by
    rw [d.curve_one]
    exact congrArg d.point (i.symm.dst_eq f)
  interior_injective e f s t hs ht h := by
    obtain ⟨hef,hst⟩ := d.interior_injective _ _ s t hs ht h
    exact ⟨i.edge.symm.injective hef,hst⟩
  interior_avoids e t ht v := d.interior_avoids _ t ht _

/-- Relabeling leaves the entire drawn subset fixed. -/
@[simp] theorem support_transport (d : PlaneDrawing G) (i : IncidenceEquiv G H) :
    (d.transport i).support = d.support := by
  ext p
  simp only [support, Set.mem_union, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro (⟨w,hw⟩ | ⟨f,t,ht⟩)
    · exact Or.inl ⟨i.vertex.symm w,hw⟩
    · exact Or.inr ⟨i.edge.symm f,t,ht⟩
  · rintro (⟨v,hv⟩ | ⟨e,t,ht⟩)
    · exact Or.inl ⟨i.vertex v,by simpa [transport] using hv⟩
    · exact Or.inr ⟨i.edge e,t,by simpa [transport] using ht⟩

@[simp] theorem cofacial_transport_iff (d : PlaneDrawing G) (i : IncidenceEquiv G H)
    (u v : V) : (d.transport i).Cofacial (i.vertex u) (i.vertex v) ↔ d.Cofacial u v := by
  simp only [Cofacial, support_transport]
  simp only [transport, Equiv.symm_apply_apply]

@[simp] theorem outerCofacial_transport_iff (d : PlaneDrawing G) (i : IncidenceEquiv G H)
    (u v : V) :
    (d.transport i).OuterCofacial (i.vertex u) (i.vertex v) ↔ d.OuterCofacial u v := by
  simp only [OuterCofacial, support_transport]
  simp only [transport, Equiv.symm_apply_apply]

end PlaneDrawing

/-- Ordinary abstract planarity is invariant under actual incidence relabeling. -/
theorem IncidenceEquiv.planar_iff {V E W F : Type*} {G : MultiGraph V E}
    {H : MultiGraph W F} (i : IncidenceEquiv G H) : G.Planar ↔ H.Planar :=
  ⟨fun h => h.map (fun d => d.transport i),
    fun h => h.map (fun d => d.transport i.symm)⟩

@[simp] theorem planar_reindex_iff {V E W F : Type*} (G : MultiGraph V E)
    (v : V ≃ W) (e : E ≃ F) : (G.reindex v e).Planar ↔ G.Planar :=
  (G.reindexEquiv v e).planar_iff.symm

end PlanarHom.MultiGraph
