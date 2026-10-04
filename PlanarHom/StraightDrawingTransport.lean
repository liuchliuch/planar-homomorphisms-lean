import PlanarHom.PlacedRoutingCells
import PlanarHom.PlanarTransport
import PlanarHom.PlanarPolygonalDrawing

noncomputable section
open unitInterval
namespace PlanarHom.MultiGraph.PlaneDrawing
open IntegerStraightDrawing PositiveBlockProgram
variable {V E W F : Type} {G : MultiGraph V E} {H : MultiGraph W F}

def Straight (d : PlaneDrawing G) : Prop :=
  ∀e t,d.curve e t=affine (d.point (G.src e)) (d.point (G.dst e)) t

theorem Straight.transport {d : PlaneDrawing G} (h : d.Straight) (i : IncidenceEquiv G H) :
    (d.transport i).Straight := by
  intro e t
  change d.curve (i.edge.symm e) t=affine _ _ t
  rw [h]
  have hs := i.symm.src_eq e
  have ht := i.symm.dst_eq e
  change G.src (i.edge.symm e)=i.vertex.symm (H.src e) at hs
  change G.dst (i.edge.symm e)=i.vertex.symm (H.dst e) at ht
  rw [hs,ht]
  rfl

theorem Straight.map {d : PlaneDrawing G} (h : d.Straight) (f : C(Plane,Plane))
    (hf : Function.Injective f) (ha : ∀a b t,f (affine a b t)=affine (f a) (f b) t) :
    (mapDrawing d f hf).Straight := by
  intro e t
  change f (d.curve e t)=affine _ _ t
  rw [h,ha]
  rfl

def Straight.polygonal {d : PlaneDrawing G} (h : d.Straight) : PolygonalDrawing G where
  drawing := d
  chain e := Polygonal.Chain.segment (Set.subset_univ _)
  curve_eq e := by
    apply ContinuousMap.ext
    intro t
    rw [h]
    change affine _ _ (t:ℝ)=AffineMap.lineMap _ _ (t:ℝ)
    apply Prod.ext <;> simp [AffineMap.lineMap_apply,affine] <;> ring

end PlanarHom.MultiGraph.PlaneDrawing
