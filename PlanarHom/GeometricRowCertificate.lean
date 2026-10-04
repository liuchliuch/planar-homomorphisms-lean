import PlanarHom.PlanarityLRRealizationRotationSystem

/-! Small reflected incidence certificates for literal geometric dart rows.
Coverage checks one recorded list position for each dart; no quadratic search
through every vertex/dart pair is used. -/
noncomputable section
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization

structure GeometricRowCertificate {V E : Type} (G : MultiGraph V E)
    [DecidableEq V] [DecidableEq (Dart E)] (row : V → List (Dart E)) where
  nodup : ∀v,(row v).Nodup
  host : ∀v,(row v).all (fun a => decide ((G.dartPair a).1=v))=true
  position : Dart E → ℕ
  cover : ∀a,(row (G.dartPair a).1)[position a]?=some a

namespace GeometricRowCertificate
variable {V E : Type} {G : MultiGraph V E} [DecidableEq V] [DecidableEq (Dart E)]
variable {row : V → List (Dart E)} (h : GeometricRowCertificate G row)

def rows : RotationRows G where
  row := row
  nodup := h.nodup
  mem v a := by
    constructor
    · intro ha
      exact of_decide_eq_true ((List.all_eq_true.mp (h.host v)) a ha)
    · intro ha
      have hh:=h.cover a
      rw [ha] at hh
      obtain ⟨hi,hget⟩:=List.getElem?_eq_some_iff.mp hh
      exact List.mem_iff_getElem.mpr ⟨h.position a,hi,hget⟩

end GeometricRowCertificate
end PlanarHom
