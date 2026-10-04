import PlanarHom.OccurrenceAlternatingWordPartition
import PlanarHom.OccurrencePfaffianCycleConstancy

/-! NEW literal cycle-flip sign identity and its global constancy consequence. -/
noncomputable section
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [LinearOrder V] {G : MultiGraph V E}

theorem AlternatingCycleFlip.matchingPfaffianSign_eq {M N : Finset E}
    (flip : AlternatingCycleFlip G M N) (orientation : E → Bool)
    (hodd : boundarySign orientation flip.cycle.cycleDarts = -1) :
    G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N := by
  apply flip.wordPartition.sign_eq orientation
  rw [boundarySign_perm orientation flip.wordPartition_cycle_perm]
  exact hodd

theorem isPfaffianOrientation_of_odd_cycleFlips [Finite V] (orientation : E → Bool)
    (hodd : ∀ {M N : Finset E}, (flip : AlternatingCycleFlip G M N) →
      boundarySign orientation flip.cycle.cycleDarts = -1) :
    G.IsPfaffianOrientation orientation := by
  apply isPfaffianOrientation_of_cycleFlip_sign_eq orientation
  intro M N flip
  exact flip.matchingPfaffianSign_eq orientation (hodd flip)

end PlanarHom.MultiGraph
