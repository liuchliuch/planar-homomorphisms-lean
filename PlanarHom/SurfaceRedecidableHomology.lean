import PlanarHom.SurfaceDartRelabelHomology
import PlanarHom.FisherNumericRotationTransport

/-! NEW proof-irrelevant equality-decider transport for actual null homology. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

theorem redecidable_homology_zero_iff {sourceDec : DecidableEq (Dart E)}
    [targetDec : DecidableEq (Dart E)] (R : @RotationRows V E G sourceDec)
    (c : @cycleSpace V E _ sourceDec G R) :
    (redecidable R).homologyClass c=0 ↔ @homologyClass V E _ _ sourceDec G R c=0 := by
  have h:sourceDec=targetDec:=Subsingleton.elim _ _
  subst targetDec
  rfl

end PlanarHom.PlanarityLRRealization.RotationRows
