import PlanarHom.PlanarTerminalStraightening
import PlanarHom.PlanarStraightSlitNormalization
import PlanarHom.PlanarFaces
import PlanarHom.PlanarRibbonExistence

/-!
# Unrestricted insertion of finite planar edge gadgets

The original outer-face condition on an ordinary finite gadget drawing now
produces an actual unit-strip drawing: cofacial augmentation, polygonal external
access, explicit finite segment collapses, affine normalization, and the explicit
slit opening supply every geometric step. Combined with unrestricted host
ribbons, insertion preserves the original ordinary planarity predicate.
-/

noncomputable section
namespace PlanarHom.TwoTerminal
open MultiGraph
variable {W F : Type*} [Finite W] [Finite F] {K : TwoTerminal W F}

/-- Every finite gadget satisfying the original ordinary outer-face definition
admits the genuine geometric strip needed by edge insertion. -/
theorem PlanarEdgeGadget.exists_stripDrawing (h : PlanarEdgeGadget K) :
    Nonempty (StripDrawing K) := by
  obtain ⟨d,hd⟩ := h
  have hne : (Sum.inl false : Bool ⊕ W) ≠ Sum.inl true := by simp
  obtain ⟨D,hcontact⟩ := hd.cofacial.exists_straightTerminalDrawing hne
  obtain ⟨N,hN,hleft,hright⟩ := D.exists_normalizedSlitDrawing hne hcontact
  exact ⟨stripDrawingOfSlit N hN hleft hright⟩

/-- Actual strip geometry is equivalent to the original finite ordinary
outer-cofacial gadget promise. It is an output witness, not extra input data. -/
theorem planarEdgeGadget_iff_stripDrawing (K : TwoTerminal W F) :
    PlanarEdgeGadget K ↔ Nonempty (StripDrawing K) :=
  ⟨PlanarEdgeGadget.exists_stripDrawing,fun ⟨d⟩ => d.planarEdgeGadget⟩

end PlanarHom.TwoTerminal

namespace PlanarHom.MultiGraph

/-- Inserting an arbitrary finite ordinary planar outer-cofacial two-terminal
gadget into every occurrence of a finite ordinary planar multigraph preserves
ordinary planarity. Loops and parallel edge occurrences remain permitted. -/
theorem Planar.insert {V E W F : Type*} [Finite V] [Finite E] [Finite W] [Finite F]
    {G : MultiGraph V E} {K : TwoTerminal W F}
    (hG : G.Planar) (hK : TwoTerminal.PlanarEdgeGadget K) : (G.insert K).Planar := by
  obtain ⟨d⟩ := hG.exists_ribbonDrawing
  obtain ⟨k⟩ := hK.exists_stripDrawing
  exact d.insert_planar k

end PlanarHom.MultiGraph
