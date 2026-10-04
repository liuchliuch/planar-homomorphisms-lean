import PlanarHom.CircleBoundaryArcRanges

/-! NEW actual host-circle corner paths. Both ordinary and wraparound corners
join the exact maximum/minimum endpoints used by the tree-strip contour sides. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.CirclePoleChart
open MultiGraph RadialPottsAssemblyGeometry

def unrotate (p q : Plane) : Plane := (p.2*q.1+p.1*q.2,-p.1*q.1+p.2*q.2)

theorem rotate_unrotate {p : Plane} (hp : rayLength p=1) (q : Plane) : rotate p (unrotate p q)=q := by
  apply Prod.ext
  · change p.2*(p.2*q.1+p.1*q.2)-p.1*(-p.1*q.1+p.2*q.2)=q.1
    calc _=(p.1^2+p.2^2)*q.1 := by ring
         _=q.1 := by rw [unit_sq hp,one_mul]
  · change p.1*(p.2*q.1+p.1*q.2)+p.2*(-p.1*q.1+p.2*q.2)=q.2
    calc _=(p.1^2+p.2^2)*q.2 := by ring
         _=q.2 := by rw [unit_sq hp,one_mul]

theorem unrotate_rotate {p : Plane} (hp : rayLength p=1) (q : Plane) : unrotate p (rotate p q)=q :=
  rotate_injective hp (rotate_unrotate hp (rotate p q))

theorem unrotate_injective {p : Plane} (hp : rayLength p=1) : Function.Injective (unrotate p) := by
  intro q r h
  have hh := congrArg (rotate p) h
  simpa only [rotate_unrotate hp] using hh

theorem unrotate_rayLength {p : Plane} (hp : rayLength p=1) (q : Plane) :
    rayLength (unrotate p q)=rayLength q := by
  have hs : (unrotate p q).1^2+(unrotate p q).2^2=q.1^2+q.2^2 := by
    calc _=(p.1^2+p.2^2)*(q.1^2+q.2^2) := by dsimp [unrotate]; ring
         _=q.1^2+q.2^2 := by rw [unit_sq hp,one_mul]
  unfold rayLength
  rw [hs]

end PlanarHom.CirclePoleChart

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart CircleBoundaryArcs
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)

/-- The actual rotation/scale/translation from chart circle to the original host. -/
def hostCircleMap : C(Plane,Plane) where
  toFun p := d.drawing.point v+C.radius • CirclePoleChart.unrotate H.pole p
  continuous_toFun := by unfold CirclePoleChart.unrotate; fun_prop

theorem hostCircleMap_injective : Function.Injective (C.hostCircleMap H) := by
  intro p q h
  have hh : CirclePoleChart.unrotate H.pole p=CirclePoleChart.unrotate H.pole q :=
    (smul_right_injective _ C.radius_pos.ne') (add_left_cancel h)
  exact CirclePoleChart.unrotate_injective H.pole_circle hh

theorem hostCircleMap_port (a : HostDart G v) (s : I) :
    C.hostCircleMap H (diskMap (0,H.height a s))=C.port a.val s := by
  rw [H.realizes]
  change d.drawing.point v+C.radius • CirclePoleChart.unrotate H.pole
    (CirclePoleChart.rotate H.pole (normalizedFan F a.val s))=C.port a.val s
  rw [CirclePoleChart.unrotate_rotate H.pole_circle,C.port_formula,a.property]

theorem hostCircleMap_circle {p : Plane} (hp : rayLength p=1) :
    rayLength (C.hostCircleMap H p-d.drawing.point v)=C.radius := by
  change rayLength ((d.drawing.point v+C.radius • CirclePoleChart.unrotate H.pole p)-d.drawing.point v)=_
  rw [add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    CirclePoleChart.unrotate_rayLength H.pole_circle,hp,mul_one]

/-- Direct increasing finite-height corner from exit a to entry b. -/
def finiteCorner (a b : HostDart G v) : C(I,Plane) :=
  (C.hostCircleMap H).comp (finiteArc (H.upper a) (H.lower b)).toContinuousMap

/-- The last-to-first corner passing through the constructed omitted pole. -/
def wrappingCorner (a b : HostDart G v) : C(I,Plane) :=
  (C.hostCircleMap H).comp (wrappingArc (H.upper a) (H.lower b)).toContinuousMap

@[simp] theorem finiteCorner_zero (a b : HostDart G v) :
    C.finiteCorner H a b 0=C.port a.val (exitParameter positive a.val) := by
  change C.hostCircleMap H (finiteArc (H.upper a) (H.lower b) 0)=_
  rw [Path.source,H.upper_eq_exit,C.hostCircleMap_port]

@[simp] theorem finiteCorner_one (a b : HostDart G v) :
    C.finiteCorner H a b 1=C.port b.val (enterParameter positive b.val) := by
  change C.hostCircleMap H (finiteArc (H.upper a) (H.lower b) 1)=_
  rw [Path.target,H.lower_eq_enter,C.hostCircleMap_port]

@[simp] theorem wrappingCorner_zero (a b : HostDart G v) :
    C.wrappingCorner H a b 0=C.port a.val (exitParameter positive a.val) := by
  change C.hostCircleMap H (wrappingArc (H.upper a) (H.lower b) 0)=_
  rw [Path.source,H.upper_eq_exit,C.hostCircleMap_port]

@[simp] theorem wrappingCorner_one (a b : HostDart G v) :
    C.wrappingCorner H a b 1=C.port b.val (enterParameter positive b.val) := by
  change C.hostCircleMap H (wrappingArc (H.upper a) (H.lower b) 1)=_
  rw [Path.target,H.lower_eq_enter,C.hostCircleMap_port]

theorem finiteCorner_injective {a b : HostDart G v} (hab : H.upper a<H.lower b) :
    Function.Injective (C.finiteCorner H a b) :=
  (C.hostCircleMap_injective H).comp (finiteArc_injective hab.ne)

theorem wrappingCorner_injective {a b : HostDart G v} (hba : H.lower b<H.upper a) :
    Function.Injective (C.wrappingCorner H a b) :=
  (C.hostCircleMap_injective H).comp (wrappingArc_injective hba)

theorem finiteCorner_circle (a b : HostDart G v) (t : I) :
    rayLength (C.finiteCorner H a b t-d.drawing.point v)=C.radius :=
  C.hostCircleMap_circle H (finiteArc_circle _ _ t)

theorem wrappingCorner_circle (a b : HostDart G v) (t : I) :
    rayLength (C.wrappingCorner H a b t-d.drawing.point v)=C.radius :=
  C.hostCircleMap_circle H (wrappingArc_circle _ _ t)

/-- Circle corners cannot meet the interior of any clipped band occurrence. -/
theorem finiteCorner_ne_band_interior (a b : HostDart G v) (t : I) (e : E) (p : I×I)
    (hp : Inside p.1) : C.finiteCorner H a b t≠C.band Function.injective_id e p := by
  intro h
  have hc := C.finiteCorner_circle H a b t
  rw [h] at hc
  exact (C.band_outside Function.injective_id e p hp v).ne hc.symm

theorem wrappingCorner_ne_band_interior (a b : HostDart G v) (t : I) (e : E) (p : I×I)
    (hp : Inside p.1) : C.wrappingCorner H a b t≠C.band Function.injective_id e p := by
  intro h
  have hc := C.wrappingCorner_circle H a b t
  rw [h] at hc
  exact (C.band_outside Function.injective_id e p hp v).ne hc.symm

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
