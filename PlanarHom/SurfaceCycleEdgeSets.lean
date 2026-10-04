import PlanarHom.SurfaceNullCycleSigns

/-! NEW exact conversion between literal F2 closed chains and actual even
occurrence subsets. It is a coordinate test, not a search through edge subsets. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

def cycleEdgeSet (c : R.cycleSpace) : Finset E := Finset.univ.filter (fun e=>c.val e=1)

@[simp] theorem mem_cycleEdgeSet (c : R.cycleSpace) (e : E) : e∈R.cycleEdgeSet c↔c.val e=1 := by
  simp [cycleEdgeSet]

theorem cycleEdgeSet_indicator (c : R.cycleSpace) : edgeIndicator (R.cycleEdgeSet c)=c.val := by
  funext e
  simp only [edgeIndicator,mem_cycleEdgeSet]
  generalize c.val e=x
  fin_cases x <;> decide

theorem cycleEdgeSet_even (c : R.cycleSpace) : G.EvenSubgraph (R.cycleEdgeSet c) := by
  intro v
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [←G.boundary_edgeIndicator,R.cycleEdgeSet_indicator]
  exact congrFun c.property v

theorem evenSubgraphCycle_cycleEdgeSet (c : R.cycleSpace) :
    R.evenSubgraphCycle (R.cycleEdgeSet c) (R.cycleEdgeSet_even c)=c :=
  Subtype.ext (R.cycleEdgeSet_indicator c)

end PlanarHom.PlanarityLRRealization.RotationRows
