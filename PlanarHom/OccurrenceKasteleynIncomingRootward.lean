import PlanarHom.IncomingLaneComposition
import PlanarHom.OccurrenceKasteleynRootwardSupport

/-! NEW geometric induction step for whole incoming subtree paths. Exact disk
and band support makes their joins simple and separates all joined families.
Local original ports and nontrivial child paths are handled by the same API. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)
variable (p : HostDart G v) (n : ℕ) (input : Fin n → HostDart G v × I)
variable (incoming : ∀ i, IncomingLane (C.port (input i).1.val (input i).2))

def joinedRootward (i : Fin n) := (incoming i).join (C.rootwardStep H p n input i)

theorem incoming_rootward_intersection
    (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (hcontact : ∀ i x, x∈(incoming i).trace → rayLength (x-d.drawing.point v)≤C.radius →
      x=C.port (input i).1.val (input i).2)
    (hband : ∀ i, Disjoint (incoming i).trace (Set.range (C.band Function.injective_id p.val.1)))
    (i j : Fin n) (x : Plane) (hxi : x∈(incoming i).trace)
    (hxj : x∈Set.range (C.rootwardStep H p n input j)) :
    x=C.port (input i).1.val (input i).2 := by
  rcases C.rootwardStep_range_subset H p n input hout j hxj with hx | hx
  · exact hcontact i x hxi hx
  · exact False.elim (Set.disjoint_left.mp (hband i) hxi hx)

theorem joinedRootward_injective
    (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (hsimple : ∀ i, (incoming i).Simple)
    (hcontact : ∀ i x, x∈(incoming i).trace → rayLength (x-d.drawing.point v)≤C.radius →
      x=C.port (input i).1.val (input i).2)
    (hband : ∀ i, Disjoint (incoming i).trace (Set.range (C.band Function.injective_id p.val.1)))
    (i : Fin n) : Function.Injective (C.joinedRootward H p n input incoming i) :=
  (incoming i).join_injective _ (hsimple i) (C.rootwardStep_injective H p n input hout i)
    (C.incoming_rootward_intersection H p n input incoming hout hcontact hband i i)

theorem joinedRootwards_disjoint
    (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (horder : ∀ i j, i<j → AfterGapOrder (H.lower p) (H.upper p)
      (H.height (input i).1 (input i).2) (H.height (input j).1 (input j).2))
    (hdisj : ∀ i j, i≠j → Disjoint (incoming i).trace (incoming j).trace)
    (hcontact : ∀ i x, x∈(incoming i).trace → rayLength (x-d.drawing.point v)≤C.radius →
      x=C.port (input i).1.val (input i).2)
    (hband : ∀ i, Disjoint (incoming i).trace (Set.range (C.band Function.injective_id p.val.1)))
    (i j : Fin n) (hne : i≠j) :
    Disjoint (Set.range (C.joinedRootward H p n input incoming i))
      (Set.range (C.joinedRootward H p n input incoming j)) := by
  apply IncomingLane.joined_families_disjoint incoming (C.rootwardStep H p n input) hdisj
    (C.rootwardSteps_disjoint H p n input hout horder) _ i j hne
  intro i j hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have he := C.incoming_rootward_intersection H p n input incoming hout hcontact hband i j x hxi hxj
  exact Set.disjoint_left.mp (C.rootwardSteps_disjoint H p n input hout horder i j hne)
    ⟨0,(Path.source _).trans he.symm⟩ hxj

/-- The joined trace is exactly the old child trace plus the actual new local
step, so set-valued subtree support invariants are preserved transparently. -/
theorem joinedRootward_range (i : Fin n) :
    Set.range (C.joinedRootward H p n input incoming i)=
      (incoming i).trace ∪ Set.range (C.rootwardStep H p n input i) :=
  (incoming i).join_range _

theorem joinedRootward_range_subset (hout : ∀ i, (input i).1.val.1≠p.val.1) (i : Fin n) :
    Set.range (C.joinedRootward H p n input incoming i) ⊆
      (incoming i).trace ∪ {x | rayLength (x-d.drawing.point v)≤C.radius} ∪
        Set.range (C.band Function.injective_id p.val.1) := by
  rw [C.joinedRootward_range]
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · rcases C.rootwardStep_range_subset H p n input hout i hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
