import PlanarHom.StraightDrawingTransport
import PlanarHom.PlanarityLRRealizationGermPieces

noncomputable section
open unitInterval
namespace PlanarHom.MultiGraph.PlaneDrawing
open IntegerStraightDrawing PlanarityLRRealization Kasteleyn
variable {V E : Type} {G : MultiGraph V E}

def endpointRay (d : PlaneDrawing G) (a : Dart E) : Plane :=
  d.point (G.dartPair a).2-d.point (G.dartPair a).1

theorem Straight.germ {d : PlaneDrawing G} (h : d.Straight) (a : Dart E) :
    StraightGerm (d.dartPath a) (d.point (G.dartPair a).1) (d.endpointRay a) := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro t _
  obtain ⟨e,b⟩:=a
  cases b
  · change d.curve e (unitInterval.symm t)=d.point (G.dst e)+(1*(t:ℝ)) • (d.point (G.src e)-d.point (G.dst e))
    rw [h]
    apply Prod.ext <;> simp [affine] <;> ring
  · change d.curve e t=d.point (G.src e)+(1*(t:ℝ)) • (d.point (G.dst e)-d.point (G.src e))
    rw [h]
    apply Prod.ext <;> simp [affine] <;> ring

end PlanarHom.MultiGraph.PlaneDrawing
