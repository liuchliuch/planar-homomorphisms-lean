import PlanarHom.PlanarVariableTrimming
import PlanarHom.PlanarFaceBridgeCores
import PlanarHom.RadialCoreGeometry
import PlanarHom.PlanarEdgeOperations
import Mathlib.Data.Finite.Sum

/-!
# Edge augmentation from ordinary cofaciality

A compact bridge in the original drawing's complementary face supplies a new
core. Vertex-dependent truncation radii keep that core disjoint from the old
cores and all vertex balls. The resulting finite radial geometry admits an
ordinary polygonal drawing of the augmented multigraph.
-/

noncomputable section
open Set unitInterval
open Classical
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Adding an occurrence between distinct vertices incident to the same actual
face preserves ordinary planarity, even when the original drawing is merely
continuous. -/
theorem Cofacial.exists_withEdge_polygonalDrawing [Finite V] [Finite E] {d : PlaneDrawing G}
    {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) :
    Nonempty (PolygonalDrawing (G.withEdge u v)) := by
  obtain ⟨r,hr0,hr⟩ := d.exists_vertex_radius
  obtain ⟨B⟩ := hface.exists_faceBridgeCore huv hr0 (d.radius_vertex_separation hr huv)
  obtain ⟨rho,hpos,hle,hu,hv,hBout⟩ := B.exists_radii hr0
  have hsep : ∀ w p, p ∈ d.forbidden w → 4*rho w < dist p (d.point w) := by
    intro w p hp
    have := hr w p hp
    have := hle w
    linarith
  let T := d.variableTrimming hpos hsep
  have hmiddle_support : ∀ e, T.middle e ⊆ d.support := by
    rintro e x ⟨t,ht,rfl⟩
    exact Or.inr (Set.mem_iUnion.mpr ⟨e,t,rfl⟩)
  have hport_support : ∀ p, T.port p ∈ d.support :=
    fun p => hmiddle_support p.1 (T.port_mem_middle p)
  let newPort : Bool → Plane := fun b => if b then B.right else B.left
  have hnew_mem : ∀ b, newPort b ∈ B.core := by
    intro b
    cases b
    · exact B.left_mem
    · exact B.right_mem
  have hnew_injective : Function.Injective newPort := by
    intro b c h
    cases b <;> cases c
    · rfl
    · exact (B.distinct h).elim
    · exact (B.distinct h.symm).elim
    · rfl
  let port : (E ⊕ Unit) × Bool → Plane :=
    fun p => Sum.elim (fun e => T.port (e,p.2)) (fun _ => newPort p.2) p.1
  have hport_injective : Function.Injective port := by
    rintro ⟨e | ⟨⟩,b⟩ ⟨f | ⟨⟩,c⟩ h
    · have hp : (e,b) = (f,c) := T.port_injective h
      cases hp
      rfl
    · change T.port (e,b) = newPort c at h
      exact (B.avoids (hnew_mem c) (h ▸ hport_support (e,b))).elim
    · change newPort b = T.port (f,c) at h
      exact (B.avoids (hnew_mem b) (h.symm ▸ hport_support (f,c))).elim
    · have hbc : b = c := hnew_injective h
      subst c
      rfl
  let middle : E ⊕ Unit → Set Plane := Sum.elim T.middle (fun _ => B.core)
  have hsphere : ∀ p, dist (port p) (d.point ((G.withEdge u v).halfVertex p)) =
      rho ((G.withEdge u v).halfVertex p) := by
    rintro ⟨e | ⟨⟩,b⟩
    · simpa only [port,halfVertex,withEdge,Sum.elim_inl,VariableTrimming.portVertex]
        using T.port_distance (e,b)
    · cases b
      · change dist B.left (d.point u) = rho u
        rw [hu]
        exact B.left_sphere
      · change dist B.right (d.point v) = rho v
        rw [hv]
        exact B.right_sphere
  have hcompact : ∀ e, IsCompact (middle e) := by
    rintro (e | ⟨⟩)
    · exact T.isCompact_middle e
    · exact B.isCompact
  have hconnected : ∀ e, IsConnected (middle e) := by
    rintro (e | ⟨⟩)
    · exact T.isConnected_middle e
    · exact B.isConnected
  have hport : ∀ p, port p ∈ middle p.1 := by
    rintro ⟨e | ⟨⟩,b⟩
    · exact T.port_mem_middle (e,b)
    · exact hnew_mem b
  have hdisjoint : ∀ {e f}, e ≠ f → Disjoint (middle e) (middle f) := by
    rintro (e | ⟨⟩) (f | ⟨⟩) hef
    · exact T.middle_disjoint (fun he => hef (congrArg Sum.inl he))
    · apply Set.disjoint_left.mpr
      intro x hx hB
      exact B.avoids hB (hmiddle_support e hx)
    · apply Set.disjoint_left.mpr
      intro x hB hx
      exact B.avoids hB (hmiddle_support f hx)
    · exact (hef rfl).elim
  have houtside : ∀ e x, x ∈ middle e → ∀ w, rho w ≤ dist x (d.point w) := by
    rintro (e | ⟨⟩) x hx w
    · obtain ⟨t,ht,rfl⟩ := hx
      exact T.middle_outside hpos hsep e t ht w
    · exact hBout x hx w
  let geometry : RadialCoreGeometry (G.withEdge u v) :=
    RadialCoreGeometry.ofMetric (G.withEdge u v) d.point d.point_injective rho hpos
      (d.variable_radius_closedBalls_disjoint hpos hsep) port hport_injective hsphere
      middle hcompact hconnected hport hdisjoint houtside
  exact geometry.exists_polygonalDrawing

/-- Cofacial augmentation preserves ordinary planarity. -/
theorem Cofacial.withEdge_planar [Finite V] [Finite E] {d : PlaneDrawing G}
    {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) :
    (G.withEdge u v).Planar := by
  obtain ⟨P⟩ := hface.exists_withEdge_polygonalDrawing huv
  exact P.planar

/-- In particular, distinct vertices on a common actual outer face can be joined
by a new occurrence while preserving ordinary planarity. -/
theorem OuterCofacial.withEdge_planar [Finite V] [Finite E] {d : PlaneDrawing G}
    {u v : V} (hface : d.OuterCofacial u v) (huv : u ≠ v) :
    (G.withEdge u v).Planar :=
  hface.cofacial.withEdge_planar huv

end PlanarHom.MultiGraph.PlaneDrawing
