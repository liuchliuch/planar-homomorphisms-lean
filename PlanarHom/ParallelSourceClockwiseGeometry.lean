import PlanarHom.ParallelSourceFanOrder
import PlanarHom.RadialPottsAssemblyRibbonCircleClip

/-! Actual compatible geometry of inherited parallel-copy rows. All ribbons,
polygonal slice chains, straight endpoint germs and strict clockwise order
are constructed from the supplied source drawing, preserving its rotation. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E}

 theorem exists_clockwise_parallel (d : PolygonalDrawing G) (ray : Dart E→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (ray a))
    (R : RotationRows G) (hne : ∀a,(ray a).1≠0)
    (hrows : ∀v,(R.row v).Pairwise (fun a b=>ClockwiseRayOrder (ray a) (ray b))) (t : ℕ) :
    ∃p : PolygonalDrawing (G.thicken t),∃rays : Dart (E×Fin t)→Plane,
      (∀a,StraightGerm (p.drawing.dartPath a) (p.drawing.point ((G.thicken t).dartPair a).1) (rays a)) ∧
      (∀a,(rays a).1≠0) ∧
      (∀v,((rows R t).row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b))) := by
  obtain ⟨S,F,_⟩ := d.exists_refined_fans_and_circleClippings true ray hgerm
  obtain ⟨w,hw,hw1,hn,ho⟩ := exists_parallel_fan_width S ray F R hne hrows t
  let level := narrowedLevel (t:=t) w hw hw1
  have hi : Function.Injective level := narrowedLevel_injective w hw hw1
  refine ⟨S.parallelPolygonalDrawing true level hi,copyRay S ray F w,?_,hn,ho⟩
  intro a
  exact S.parallel_straightGerm true level hi ray F a.1 a.2
end PlanarHom.ParallelSource
