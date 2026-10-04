import PlanarHom.OccurrenceMatchingCycleConnectivity

/-! NEW constancy transport along the proved literal occurrence-cycle flips. -/
noncomputable section
namespace PlanarHom.MultiGraph
variable {V E : Type*} [Finite V] [LinearOrder V] {G : MultiGraph V E}

theorem isPfaffianOrientation_of_cycleFlip_sign_eq (orientation : E → Bool)
    (hflip : ∀ {M N : Finset E}, AlternatingCycleFlip G M N →
      G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N) :
    G.IsPfaffianOrientation orientation := by
  intro M N hM hN
  have hp := hM.cycleFlip_connected hN
  induction hp with
  | refl => rfl
  | @tail B C hpath hstep ih =>
    obtain ⟨flip⟩ := hstep
    exact (ih flip.left_perfect).trans (hflip flip)

end PlanarHom.MultiGraph
