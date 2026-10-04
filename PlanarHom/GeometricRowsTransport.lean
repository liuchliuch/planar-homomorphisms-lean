import PlanarHom.RotationRowsTransport
import PlanarHom.StraightDrawingGerms
import PlanarHom.RadialPottsAssemblyGeneralRows

noncomputable section
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E W F : Type} {G : MultiGraph V E} {H : MultiGraph W F}

namespace MultiGraph.PlaneDrawing

theorem endpointRay_transport (d : PlaneDrawing G) (i : IncidenceEquiv G H) (a : Dart E) :
    (d.transport i).endpointRay (i.darts a)=d.endpointRay a := by
  obtain ⟨e,b⟩:=a
  cases b <;> simp [endpointRay,PlaneDrawing.transport,dartPair,IncidenceEquiv.darts,i.src_eq,i.dst_eq]

theorem nonvertical_transport (d : PlaneDrawing G) (i : IncidenceEquiv G H)
    (h : ∀a,(d.endpointRay a).1≠0) (a : Dart F) : ((d.transport i).endpointRay a).1≠0 := by
  have hh:=h (i.darts.symm a)
  rw [←endpointRay_transport d i,i.darts.apply_symm_apply] at hh
  exact hh

end MultiGraph.PlaneDrawing
namespace PlanarityLRRealization.RotationRows
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]

theorem clockwise_transport (R : RotationRows G) (d : PlaneDrawing G) (i : IncidenceEquiv G H)
    (h : ∀v,(R.row v).Pairwise (fun a b=>ClockwiseRayOrder (d.endpointRay a) (d.endpointRay b)))
    (w : W) : ((R.transport i).row w).Pairwise (fun a b=>
      ClockwiseRayOrder ((d.transport i).endpointRay a) ((d.transport i).endpointRay b)) := by
  simp only [transport,List.pairwise_map]
  apply (h (i.vertex.symm w)).imp
  intro a b hab
  simpa only [PlaneDrawing.endpointRay_transport] using hab

end PlanarityLRRealization.RotationRows
end PlanarHom
