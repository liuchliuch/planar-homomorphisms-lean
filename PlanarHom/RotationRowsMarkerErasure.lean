import PlanarHom.ColoringFramedCanvasRows

/-! The canonical finite marker deletion applied directly to actual geometric
row data and an explicit retained/deleted dart naming equivalence. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn FinitePermutationCycles
variable {V E A : Type} [DecidableEq (Dart E)] [DecidableEq A] [Fintype A]
variable {G : MultiGraph V E}

theorem eraseFinMarkers_eq_of_retained_rows (R : RotationRows G) (n : ℕ)
    (e : Dart E≃A⊕Fin n) (P : Equiv.Perm A)
    (h : ∀a,(((R.row (G.dartPair (e.symm (.inl a))).1).map e).filterMap
      HostRowSystem.keepLeft).formPerm a=P a) :
    eraseFinMarkers (e.permCongr R.rotation)=P := by
  let F:=HostRowSystem.ofRotationRows G R
  have he:=HostRowSystem.relabel_rotation F e
  change (F.relabel e).rotation=e.permCongr R.rotation at he
  rw [←he]
  apply HostRowSystem.eraseFinMarkers_eq_of_rows
  intro a
  exact h a

end PlanarHom.PlanarityLRRealization.RotationRows
