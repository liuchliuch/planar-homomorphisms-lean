import PlanarHom.RootedAttachment
import PlanarHom.PlanarTransport
import PlanarHom.PolygonalFaceAccess
import PlanarHom.PlanarPolygonalization
import PlanarHom.PlaneAffineNormalization
import PlanarHom.PlanarSlitOpening
import PlanarHom.SegmentCollapseData
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Gluing arbitrary finite rooted planar multigraphs

A finite polygonal drawing has a short complementary straight segment at every
vertex. Opening that slit puts the chosen vertex on a supporting line with the
rest of the drawing strictly on one side. Two such drawings fit on opposite
sides of the line, meeting only at their common root. All drawing witnesses are
constructed from ordinary planarity; loops and isolated roots are permitted.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph

/-- A nondegenerate straight segment has dense complement in the plane. -/
theorem dense_compl_plane_segment {a b : Plane} (hab : a ≠ b) :
    Dense ([a -[ℝ] b]ᶜ : Set Plane) := by
  let N := normalizeSegment b a hab.symm
  have hD : Dense ((fun p : Plane => (N p).2) ⁻¹' ({0}ᶜ : Set ℝ)) :=
    (dense_compl_singleton (0 : ℝ)).preimage (isOpenMap_snd.comp N.isOpenMap)
  apply hD.mono
  intro p hp hseg
  have hN : N p ∈ [(0,0) -[ℝ] (1,0)] := by
    rw [← normalizeSegment_image b a hab.symm]
    exact ⟨p,hseg,rfl⟩
  rw [segment_eq_image_lineMap] at hN
  obtain ⟨t,ht,hline⟩ := hN
  apply hp
  change (N p).2 = 0
  rw [← hline]
  simp [AffineMap.lineMap_apply_module]

namespace PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A finite polygonal multigraph has dense complement, including its isolated
vertices. -/
theorem dense_compl_support [Finite V] [Finite E] (d : PolygonalDrawing G) :
    Dense d.drawing.supportᶜ := by
  let A := {p : Plane × Plane // p ∈ d.segmentSet}
  letI : Finite A := d.finite_segmentSet.to_subtype
  have hseg : Dense (⋂ p : A, ([p.1.1 -[ℝ] p.1.2]ᶜ : Set Plane)) := by
    apply dense_iInter_of_isOpen
    · intro p
      have hc : IsCompact [p.1.1 -[ℝ] p.1.2] := by
        rw [segment_eq_image_lineMap]
        exact isCompact_Icc.image (by fun_prop)
      exact hc.isClosed.isOpen_compl
    · intro p
      exact dense_compl_plane_segment (d.segment_ne p.2)
  have hhost := hseg.diff_finite d.finite_hostSet
  apply hhost.mono
  intro p hp hsupport
  rcases hsupport with ⟨v,hv⟩ | he
  · exact hp.2 ⟨v,hv⟩
  · obtain ⟨e,t,ht⟩ := Set.mem_iUnion.mp he
    obtain ⟨a,b,hab,s,hs,_⟩ := (d.chain e).strictPath_joint_segment
      (d.chain_length_ne_zero e) id t
    have hpiece : (a,b) ∈ d.segmentSet := ⟨e,hab⟩
    apply (Set.mem_iInter.mp hp.1 ⟨(a,b),hpiece⟩)
    rw [← ht,d.curve_eq]
    change (d.chain e).strictPath t ∈ [a -[ℝ] b]
    rw [hs,segment_eq_image_lineMap]
    exact ⟨(s : ℝ),s.2,rfl⟩

/-- Every vertex has a nondegenerate straight access segment whose only
contact with the entire drawing is that vertex. -/
theorem exists_root_access [Finite V] [Finite E] (d : PolygonalDrawing G) (v : V) :
    ∃ q : Plane, q ≠ d.drawing.point v ∧
      ∀ w, w ∈ [d.drawing.point v -[ℝ] q] → w ∈ d.drawing.support →
        w = d.drawing.point v := by
  obtain ⟨r,hr,haccess⟩ := d.exists_access_radius v
  obtain ⟨q,hq,hqr⟩ := d.dense_compl_support.exists_mem_open Metric.isOpen_ball
    ⟨d.drawing.point v,Metric.mem_ball_self hr⟩
  refine ⟨q,?_,haccess q hqr hq⟩
  intro heq
  exact hq (Or.inl ⟨v,heq.symm⟩)

end PolygonalDrawing

namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Affine normalization of one rooted access segment produces the actual
slit domain, even though its far endpoint need not be a graph vertex. -/
theorem exists_rootSlitDrawing (d : PlaneDrawing G) (r : V)
    {q : Plane} (hq : q ≠ d.point r)
    (hcontact : ∀ w, w ∈ [d.point r -[ℝ] q] → w ∈ d.support → w = d.point r) :
    ∃ D : PlaneDrawing G, D.AvoidsOpenUnitSegment ∧ D.point r = (0,0) := by
  let N := normalizeSegment q (d.point r) hq
  let F : C(Plane,Plane) := ⟨N,N.continuous⟩
  let D := d.mapOnSupport F N.injective.injOn
  refine ⟨D,?_,normalizeSegment_center _ _ hq⟩
  intro p hp hopen
  have hsupport : p ∈ N '' d.support := by
    change p ∈ (d.mapOnSupport F N.injective.injOn).support at hp
    rw [d.support_mapOnSupport] at hp
    exact hp
  obtain ⟨w,hw,rfl⟩ := hsupport
  have haxis : N w ∈ [(0,0) -[ℝ] (1,0)] := by
    rw [segment_eq_image_lineMap]
    refine ⟨(N w).1,⟨hopen.1.le,hopen.2.1.le⟩,?_⟩
    apply Prod.ext <;> simp [AffineMap.lineMap_apply_module,hopen.2.2]
  have hsegment : w ∈ [d.point r -[ℝ] q] := by
    rw [← normalizeSegment_preimage q (d.point r) hq]
    exact haxis
  have heq : w = d.point r := hcontact w hsegment hw
  have hz : N w = (0,0) := heq ▸ normalizeSegment_center _ _ hq
  rw [hz] at hopen
  exact (lt_irrefl 0) hopen.1

/-- Open a complementary unit slit using the explicit injective square map. -/
def openSlit (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment) : PlaneDrawing G where
  point v := TwoTerminal.StripDrawing.squareInPlane (SlitOpening.toSquare (d.slitPoint h v))
  point_injective := by
    intro v w he
    apply d.point_injective
    exact congrArg Subtype.val (SlitOpening.toSquare_injective
      (TwoTerminal.StripDrawing.squareInPlane_injective he))
  curve e := TwoTerminal.StripDrawing.squareInPlane.comp
    (SlitOpening.toSquare.comp (d.slitCurve h e))
  curve_zero e := by simp
  curve_one e := by simp
  interior_injective e f s t hs ht he :=
    d.interior_injective e f s t hs ht (congrArg Subtype.val
      (SlitOpening.toSquare_injective (TwoTerminal.StripDrawing.squareInPlane_injective he)))
  interior_avoids e t ht v he :=
    d.interior_avoids e t ht v (congrArg Subtype.val
      (SlitOpening.toSquare_injective (TwoTerminal.StripDrawing.squareInPlane_injective he)))

@[simp] theorem openSlit_root (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment)
    {r : V} (hr : d.point r = (0,0)) : (d.openSlit h).point r = (0,0) := by
  change (SlitOpening.horizontal (d.point r),SlitOpening.height (d.point r)) = _
  simp [hr]

theorem openSlit_point_pos (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment)
    {r v : V} (hr : d.point r = (0,0)) (hv : v ≠ r) :
    0 < ((d.openSlit h).point v).1 := by
  apply SlitOpening.horizontal_pos
  intro heq
  exact hv (d.point_injective (heq.trans hr.symm))

theorem openSlit_curve_pos (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment)
    {r : V} (hr : d.point r = (0,0)) (e : E) (t : I) (ht : Inside t) :
    0 < ((d.openSlit h).curve e t).1 := by
  apply SlitOpening.horizontal_pos
  intro heq
  exact d.interior_avoids e t ht r (heq.trans hr.symm)

end PlaneDrawing

/-- A drawing with its prescribed root at the origin and every other vertex
and open edge interior strictly in the right half-plane. -/
structure RootHalfPlaneDrawing {V E : Type*} (G : MultiGraph V E) (r : V) where
  drawing : PlaneDrawing G
  root_zero : drawing.point r = (0,0)
  point_pos : ∀ v, v ≠ r → 0 < (drawing.point v).1
  curve_pos : ∀ e t, Inside t → 0 < (drawing.curve e t).1

/-- Every finite ordinary planar drawing can be redrawn with any prescribed
vertex on a supporting line, including a vertex incident only to loops or no edges. -/
theorem Planar.exists_rootHalfPlaneDrawing {V E : Type*} [Finite V] [Finite E]
    {G : MultiGraph V E} (h : G.Planar) (r : V) : Nonempty (RootHalfPlaneDrawing G r) := by
  obtain ⟨P⟩ := h.exists_polygonalDrawing
  obtain ⟨q,hq,hcontact⟩ := P.exists_root_access r
  obtain ⟨d,hd,hr⟩ := P.drawing.exists_rootSlitDrawing r hq hcontact
  exact ⟨⟨d.openSlit hd,d.openSlit_root hd hr,
    fun v hv => d.openSlit_point_pos hd hr hv,fun e t ht => d.openSlit_curve_pos hd hr e t ht⟩⟩

namespace RootHalfPlaneDrawing
variable {V W E F : Type*} {G : MultiGraph V E} {H : RootedGraph W F} {r : V}

theorem point_nonneg (d : RootHalfPlaneDrawing G r) (v : V) :
    0 ≤ (d.drawing.point v).1 := by
  by_cases hv : v = r
  · subst v
    rw [d.root_zero]
  · exact (d.point_pos v hv).le

/-- Reflection across the root's supporting line. -/
def reflect : C(Plane,Plane) where
  toFun p := (-p.1,p.2)
  continuous_toFun := by fun_prop

theorem reflect_injective : Function.Injective reflect := by
  intro p q h
  apply Prod.ext
  · have := congrArg Prod.fst h
    simpa [reflect] using this
  · simpa [reflect] using congrArg Prod.snd h

@[simp] theorem reflect_zero : reflect (0,0) = (0,0) := by
  simp [reflect]

/-- The two half-plane drawings give an ordinary drawing of attachment at an
arbitrary host vertex. -/
def attachRooted (d : RootHalfPlaneDrawing G r)
    (k : RootHalfPlaneDrawing H (Sum.inl PUnit.unit)) : PlaneDrawing (G.attachRooted H r) where
  point := Sum.elim d.drawing.point (fun w => reflect (k.drawing.point (.inr w)))
  point_injective := by
    intro v w h
    cases v with
    | inl v =>
      cases w with
      | inl w => exact congrArg Sum.inl (d.drawing.point_injective h)
      | inr w =>
        have hv := d.point_nonneg v
        have hw := k.point_pos (.inr w) (by simp)
        have hh := congrArg Prod.fst h
        change (d.drawing.point v).1 = -(k.drawing.point (.inr w)).1 at hh
        exfalso; linarith
    | inr v =>
      cases w with
      | inl w =>
        have hv := k.point_pos (.inr v) (by simp)
        have hw := d.point_nonneg w
        have hh := congrArg Prod.fst h
        change -(k.drawing.point (.inr v)).1 = (d.drawing.point w).1 at hh
        exfalso; linarith
      | inr w =>
        have hh := k.drawing.point_injective (reflect_injective h)
        exact congrArg Sum.inr (Sum.inr.inj hh)
  curve := Sum.elim d.drawing.curve (fun f => reflect.comp (k.drawing.curve f))
  curve_zero := by
    intro e
    cases e with
    | inl e => exact d.drawing.curve_zero e
    | inr e =>
      change reflect (k.drawing.curve e 0) = _
      rw [k.drawing.curve_zero]
      cases he : H.src e with
      | inl u =>
        have hu : u = PUnit.unit := Subsingleton.elim _ _
        subst u
        simp [MultiGraph.attachRooted,attachRootedVertex,he,k.root_zero,d.root_zero]
      | inr w => simp [MultiGraph.attachRooted,attachRootedVertex,he]
  curve_one := by
    intro e
    cases e with
    | inl e => exact d.drawing.curve_one e
    | inr e =>
      change reflect (k.drawing.curve e 1) = _
      rw [k.drawing.curve_one]
      cases he : H.dst e with
      | inl u =>
        have hu : u = PUnit.unit := Subsingleton.elim _ _
        subst u
        simp [MultiGraph.attachRooted,attachRootedVertex,he,k.root_zero,d.root_zero]
      | inr w => simp [MultiGraph.attachRooted,attachRootedVertex,he]
  interior_injective := by
    intro e f s t hs ht h
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        obtain ⟨hef,hst⟩ := d.drawing.interior_injective e f s t hs ht h
        exact ⟨congrArg Sum.inl hef,hst⟩
      | inr f =>
        have he := d.curve_pos e s hs
        have hf := k.curve_pos f t ht
        have hh := congrArg Prod.fst h
        change (d.drawing.curve e s).1 = -(k.drawing.curve f t).1 at hh
        exfalso; linarith
    | inr e =>
      cases f with
      | inl f =>
        have he := k.curve_pos e s hs
        have hf := d.curve_pos f t ht
        have hh := congrArg Prod.fst h
        change -(k.drawing.curve e s).1 = (d.drawing.curve f t).1 at hh
        exfalso; linarith
      | inr f =>
        obtain ⟨hef,hst⟩ := k.drawing.interior_injective e f s t hs ht
          (reflect_injective h)
        exact ⟨congrArg Sum.inr hef,hst⟩
  interior_avoids := by
    intro e t ht v h
    cases e with
    | inl e =>
      cases v with
      | inl v => exact d.drawing.interior_avoids e t ht v h
      | inr v =>
        have he := d.curve_pos e t ht
        have hv := k.point_pos (.inr v) (by simp)
        have hh := congrArg Prod.fst h
        change (d.drawing.curve e t).1 = -(k.drawing.point (.inr v)).1 at hh
        linarith
    | inr e =>
      cases v with
      | inl v =>
        have he := k.curve_pos e t ht
        have hv := d.point_nonneg v
        have hh := congrArg Prod.fst h
        change -(k.drawing.curve e t).1 = (d.drawing.point v).1 at hh
        linarith
      | inr v => exact k.drawing.interior_avoids e t ht (.inr v) (reflect_injective h)

end RootHalfPlaneDrawing

/-- Attaching an arbitrary finite rooted planar multigraph at any vertex of an
ordinary finite planar host preserves ordinary planarity. -/
theorem Planar.attachRooted {V W E F : Type*} [Finite V] [Finite W] [Finite E] [Finite F]
    {G : MultiGraph V E} {H : RootedGraph W F} (hG : G.Planar) (hH : H.Planar) (r : V) :
    (G.attachRooted H r).Planar := by
  obtain ⟨d⟩ := hG.exists_rootHalfPlaneDrawing r
  obtain ⟨k⟩ := hH.exists_rootHalfPlaneDrawing (Sum.inl PUnit.unit)
  exact ⟨d.attachRooted k⟩

end PlanarHom.MultiGraph

namespace PlanarHom.RootedGraph
open MultiGraph
variable {V W E F : Type*}

/-- Rooted gluing is just attachment with reassociated vertex labels. -/
def glueIncidenceEquiv (G : RootedGraph V E) (H : RootedGraph W F) :
    IncidenceEquiv (G.attachRooted H (Sum.inl PUnit.unit)) (glue G H) where
  vertex := Equiv.sumAssoc PUnit V W
  edge := Equiv.refl (E ⊕ F)
  src_eq := by
    intro e
    cases e with
    | inl e =>
      cases he : G.src e <;> simp [glue,MultiGraph.attachRooted,he,Equiv.sumAssoc]
    | inr f =>
      cases he : H.src f with
      | inl u => cases u; simp [glue,MultiGraph.attachRooted,attachRootedVertex,he,Equiv.sumAssoc]
      | inr w => simp [glue,MultiGraph.attachRooted,attachRootedVertex,he,Equiv.sumAssoc]
  dst_eq := by
    intro e
    cases e with
    | inl e =>
      cases he : G.dst e <;> simp [glue,MultiGraph.attachRooted,he,Equiv.sumAssoc]
    | inr f =>
      cases he : H.dst f with
      | inl u => cases u; simp [glue,MultiGraph.attachRooted,attachRootedVertex,he,Equiv.sumAssoc]
      | inr w => simp [glue,MultiGraph.attachRooted,attachRootedVertex,he,Equiv.sumAssoc]

/-- Ordinary planarity is preserved by root identification for arbitrary finite
rooted occurrence multigraphs, with no outer-face or embedding input. -/
theorem glue_planar [Finite V] [Finite W] [Finite E] [Finite F]
    {G : RootedGraph V E} {H : RootedGraph W F} (hG : G.Planar) (hH : H.Planar) :
    (glue G H).Planar :=
  (glueIncidenceEquiv G H).planar_iff.mp (hG.attachRooted hH (Sum.inl PUnit.unit))

end PlanarHom.RootedGraph
