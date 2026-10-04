import PlanarHom.PlanarityLRRealizationRotationSystem
import PlanarHom.PlanarTransport

noncomputable section
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E W F : Type} {G : MultiGraph V E} {H : MultiGraph W F}
namespace MultiGraph.IncidenceEquiv

def darts (i : IncidenceEquiv G H) : Dart E ≃ Dart F := Equiv.prodCongr i.edge (Equiv.refl _)

theorem dart_host (i : IncidenceEquiv G H) (a : Dart E) :
    (H.dartPair (i.darts a)).1=i.vertex (G.dartPair a).1 := by
  obtain ⟨e,b⟩:=a
  cases b
  · exact i.dst_eq e
  · exact i.src_eq e

end MultiGraph.IncidenceEquiv

namespace PlanarityLRRealization.RotationRows
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]

def transport (R : RotationRows G) (i : IncidenceEquiv G H) : RotationRows H where
  row w := (R.row (i.vertex.symm w)).map i.darts
  nodup w := (R.nodup _).map i.darts.injective
  mem w a := by
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
      rw [i.dart_host,(R.mem _ _).mp hb,i.vertex.apply_symm_apply]
    · intro ha
      apply List.mem_map.mpr
      refine ⟨i.darts.symm a,?_,i.darts.apply_symm_apply a⟩
      apply (R.mem _ _).mpr
      apply i.vertex.injective
      rw [i.vertex.apply_symm_apply,←i.dart_host,i.darts.apply_symm_apply,ha]

end PlanarityLRRealization.RotationRows
end PlanarHom
