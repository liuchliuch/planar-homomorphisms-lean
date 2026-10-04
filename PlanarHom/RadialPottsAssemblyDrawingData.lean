import PlanarHom.RadialPottsAssemblyDegrees
import PlanarHom.RadialPottsAssemblyUnitSquare
import PlanarHom.PlaneDrawingEdgeInjectivity
import PlanarHom.PolygonalArc

/-! Local geometric data for literal radial assembly: embedded disjoint closed
bands and actual disjoint corner wires. No global drawing is an input field. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsAssemblyGeometry
variable {E : Type} {k : ℕ}

structure DrawingData (rotation : Equiv.Perm (Medial.Dart E)) (k : ℕ) where
  band : E → C(I × I, Plane)
  band_joint_injective : ∀ e f p q, band e p = band f q → e = f ∧ p = q
  wire : (Medial.Dart E × Fin k) → C(I, Plane)
  wire_joint_injective : ∀ w z s t, wire w s = wire z t → w = z ∧ s = t
  wire_zero : ∀ w, wire w 0 = band (portPreimage rotation w true).1
    (squarePoint (.inr (portPreimage rotation w true).2))
  wire_one : ∀ w, wire w 1 = band (portPreimage rotation w false).1
    (squarePoint (.inr (portPreimage rotation w false).2))
  band_ne_wire : ∀ e p w t, Inside t → band e p ≠ wire w t

namespace DrawingData
variable {rotation : Equiv.Perm (Medial.Dart E)} (B : DrawingData rotation k)

def tilePoint (e : E) (v : RadialPottsTile.Vertex k) : Plane := B.band e (squarePoint v)
def tileCurve (e : E) (f : Edge k) : C(I,Plane) := (B.band e).comp (squareCurve f)

private theorem squarePoint_injective : Function.Injective (@squarePoint k) := by
  intro v w h
  apply (squareDrawing k).point_injective
  exact congrArg (fun p : I × I => ((p.1:ℝ),(p.2:ℝ))) h

theorem tilePoint_joint_injective {e f : E} {v w : RadialPottsTile.Vertex k}
    (h : B.tilePoint e v = B.tilePoint f w) : e=f ∧ v=w := by
  obtain ⟨he,hp⟩ := B.band_joint_injective e f _ _ h
  exact ⟨he,squarePoint_injective hp⟩

@[simp] theorem tileCurve_zero (e : E) (f : Edge k) :
    B.tileCurve e f 0 = B.tilePoint e ((RadialPottsTile.graph k).src f) := by
  simp [tileCurve,tilePoint]
@[simp] theorem tileCurve_one (e : E) (f : Edge k) :
    B.tileCurve e f 1 = B.tilePoint e ((RadialPottsTile.graph k).dst f) := by
  simp [tileCurve,tilePoint]

theorem tileCurve_interior_injective {e f : E} {a b : Edge k} {s t : I}
    (hs : Inside s) (ht : Inside t) (h : B.tileCurve e a s=B.tileCurve f b t) :
    e=f ∧ a=b ∧ s=t := by
  obtain ⟨hef,hp⟩ := B.band_joint_injective e f _ _ h
  have h' := congrArg (fun p : I×I => ((p.1:ℝ),(p.2:ℝ))) hp
  have hi := (squareDrawing k).interior_injective a b s t hs ht h'
  exact ⟨hef,hi⟩

theorem tileCurve_interior_avoids {e f : E} {a : Edge k} {t : I}
    (ht : Inside t) (v : RadialPottsTile.Vertex k) :
    B.tileCurve e a t ≠ B.tilePoint f v := by
  intro h
  have hp := (B.band_joint_injective e f _ _ h).2
  exact (squareDrawing k).interior_avoids a t ht v
    (congrArg (fun p : I×I => ((p.1:ℝ),(p.2:ℝ))) hp)

theorem tileCurve_eq_point_iff (e f : E) (a : Edge k) (t : I) (v : RadialPottsTile.Vertex k) :
    B.tileCurve e a t=B.tilePoint f v ↔
      e=f ∧ ((t=0 ∧ (RadialPottsTile.graph k).src a=v) ∨
        (t=1 ∧ (RadialPottsTile.graph k).dst a=v)) := by
  constructor
  · intro h
    obtain ⟨hef,hp⟩ := B.band_joint_injective e f _ _ h
    exact ⟨hef,((squareDrawing k).curve_eq_point_iff a t v).mp
      (congrArg (fun p : I×I => ((p.1:ℝ),(p.2:ℝ))) hp)⟩
  · rintro ⟨rfl,(⟨rfl,h⟩ | ⟨rfl,h⟩)⟩ <;> simp [h]

/-- The physical point chosen for each identified terminal is the wire midpoint. -/
def point : Vertex E k → Plane
  | .inl (e,w) => B.tilePoint e (.inl w)
  | .inr w => B.wire w PlaneDrawing.half

theorem point_injective : Function.Injective B.point := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      obtain ⟨he,hp⟩ := B.tilePoint_joint_injective h
      exact congrArg Sum.inl (Prod.ext he (Sum.inl.inj hp))
    | inr w => exact (B.band_ne_wire _ _ _ _ PlaneDrawing.half_inside h).elim
  | inr v =>
    cases w with
    | inl w => exact (B.band_ne_wire _ _ _ _ PlaneDrawing.half_inside h.symm).elim
    | inr w => exact congrArg Sum.inr (B.wire_joint_injective _ _ _ _ h).1

/-- Every tile source is a white vertex; no terminal is a source. -/
theorem tile_src_white (f : Edge k) : ∃ w, (RadialPottsTile.graph k).src f=.inl w := by
  cases f <;> exact ⟨_,rfl⟩

/-- A literal terminal is the destination of at most one occurrence. -/
theorem tile_dst_port_unique {a b : Edge k} {p : Port k}
    (ha : (RadialPottsTile.graph k).dst a=.inr p)
    (hb : (RadialPottsTile.graph k).dst b=.inr p) : a=b := by
  cases a with
  | inr a => simp [RadialPottsTile.graph] at ha
  | inl a =>
    cases b with
    | inr b => simp [RadialPottsTile.graph] at hb
    | inl b =>
      apply congrArg Sum.inl
      have hh : longEndpoint (a,true)=longEndpoint (b,true) := ha.trans hb.symm
      exact congrArg Prod.fst ((longEndpoint_bijective k).1 hh)

end DrawingData
end PlanarHom.RadialPotts.Assembly
