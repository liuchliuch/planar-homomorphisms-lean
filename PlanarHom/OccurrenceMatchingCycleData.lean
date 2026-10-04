import PlanarHom.OccurrencePfaffianPairings
import PlanarHom.PlanarityLRRealizationGermPieces

/-! NEW finite occurrence-sensitive cycle data for perfect-matching flips.
A parallel two-edge alternating cycle is retained explicitly. -/
noncomputable section
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*}

def cycleNext (n : ℕ) (hn : 2≤n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ (by omega)⟩

structure DirectedSimpleCycle (G : MultiGraph V E) where
  length : ℕ
  length_ge_two : 2≤length
  vertex : Fin length→V
  vertex_injective : Function.Injective vertex
  dart : Fin length→Dart E
  edge_injective : Function.Injective (fun i=>(dart i).1)
  tail_eq : ∀i,(G.dartPair (dart i)).1=vertex i
  head_eq : ∀i,(G.dartPair (dart i)).2=vertex (cycleNext length length_ge_two i)

namespace DirectedSimpleCycle
variable {G : MultiGraph V E}

def cycleDarts (c : DirectedSimpleCycle G) : List (Dart E) := List.ofFn c.dart

def cycleEdges (c : DirectedSimpleCycle G) : Finset E := by
  classical
  exact Finset.univ.image (fun i=>(c.dart i).1)

end DirectedSimpleCycle

structure AlternatingCycleFlip (G : MultiGraph V E) (M N : Finset E) where
  cycle : DirectedSimpleCycle G
  even_length : Even cycle.length
  left_perfect : G.PerfectMatching M
  right_perfect : G.PerfectMatching N
  left_even : ∀i,(cycle.dart i).1∈M ↔ Even i.val
  right_odd : ∀i,(cycle.dart i).1∈N ↔ Odd i.val
  agree_off : ∀e,(∀i,(cycle.dart i).1≠e)→(e∈M ↔ e∈N)

def CycleFlipRel (G : MultiGraph V E) (M N : Finset E) : Prop :=
  Nonempty (AlternatingCycleFlip G M N)

end PlanarHom.MultiGraph
