import PlanarHom.PottsSourceQueryCorrectness
import PlanarHom.FisherNumericRotationTransport

/-! NEW exact transport of polygonal curves and their clockwise germs through
an orientation-preserving occurrence/vertex incidence equivalence. No drawing
is reconstructed and no cyclic row order changes. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PolygonalIncidenceTransport
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E W F : Type} {G : MultiGraph V E} {H : MultiGraph W F}

def reendpoint {a b a' b' : Plane} (c : Polygonal.Chain Set.univ a b)
    (ha : a=a') (hb : b=b') : Polygonal.Chain Set.univ a' b' := ha ▸ hb ▸ c

theorem reendpoint_path {a b a' b' : Plane} (c : Polygonal.Chain Set.univ a b)
    (ha : a=a') (hb : b=b') :
    (reendpoint c ha hb).strictPath.toContinuousMap=c.strictPath.toContinuousMap := by
  subst a'; subst b'; rfl

def drawing (d : PolygonalDrawing G) (i : IncidenceEquiv G H) : PolygonalDrawing H where
  drawing:=d.drawing.transport i
  chain f:=reendpoint (d.chain (i.edge.symm f))
    (congrArg d.drawing.point (i.symm.src_eq f)) (congrArg d.drawing.point (i.symm.dst_eq f))
  curve_eq f:=by
    rw [reendpoint_path]
    exact d.curve_eq (i.edge.symm f)

theorem dartPath (d : PlaneDrawing G) (i : IncidenceEquiv G H) (a : Dart E) :
    (d.transport i).dartPath (i.dartRelabel.dart a)=d.dartPath a := by
  rcases a with ⟨e,b⟩
  cases b <;> ext s <;>
    simp [PlaneDrawing.dartPath,PlaneDrawing.transport,IncidenceEquiv.dartRelabel]

theorem clockwise (d : PolygonalDrawing G) (i : IncidenceEquiv G H)
    [DecidableEq (Dart E)] [DecidableEq (Dart F)]
    (R : RotationRows G) (ray : Dart E→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a)
      (d.drawing.point (G.dartPair a).1) (ray a))
    (hne : ∀a,(ray a).1≠0)
    (hrows : ∀v,(R.row v).Pairwise (fun a b=>ClockwiseRayOrder (ray a) (ray b))) :
    ∃p : PolygonalDrawing H,∃rays : Dart F→Plane,
      (∀a,StraightGerm (p.drawing.dartPath a) (p.drawing.point (H.dartPair a).1) (rays a)) ∧
      (∀a,(rays a).1≠0) ∧
      (∀v,((i.dartRelabel.rows R).row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b))) := by
  let rayH : Dart F→Plane := fun a=>ray (i.dartRelabel.dart.symm a)
  refine ⟨drawing d i,rayH,?_,fun a=>hne _,?_⟩
  · intro b
    let a:=i.dartRelabel.dart.symm b
    have he : i.dartRelabel.dart a=b := i.dartRelabel.dart.apply_symm_apply b
    rw [←he]
    change StraightGerm ((d.drawing.transport i).dartPath (i.dartRelabel.dart a))
      ((d.drawing.transport i).point (H.dartPair (i.dartRelabel.dart a)).1) (rayH (i.dartRelabel.dart a))
    rw [dartPath,i.dartRelabel.host]
    simpa only [PlaneDrawing.transport,IncidenceEquiv.dartRelabel,Equiv.symm_apply_apply,rayH] using hgerm a
  · intro v
    change ((R.row (i.vertex.symm v)).map i.dartRelabel.dart).Pairwise _
    rw [List.pairwise_map]
    simpa only [Function.comp_apply,rayH,Equiv.symm_apply_apply] using hrows (i.vertex.symm v)

end PlanarHom.PolygonalIncidenceTransport
