import PlanarHom.OccurrenceMatchingCycleData
import Mathlib.Logic.Equiv.Fin.Rotate

/-! NEW exact occurrence degrees of the concrete simple directed cycle. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E}

theorem cycleNext_eq_finRotate (n : ℕ) (hn : 2≤n) (i : Fin n) : cycleNext n hn i=finRotate n i := by
  cases n with
  | zero => omega
  | succ n =>
      apply Fin.ext
      rw [finRotate_succ_apply,Fin.val_add]
      change (i.val+1)%(n+1)=(i.val+(1:Fin (n+1)).val)%(n+1)
      congr 2
      change 1=1%(n+1)
      exact (Nat.mod_eq_of_lt (by omega)).symm

namespace DirectedSimpleCycle

def cycleVertices (c : DirectedSimpleCycle G) : Finset V := by
  classical
  exact Finset.univ.image c.vertex

theorem endpointCount_dart (a : Dart E) (v : V) :
    G.endpointCount a.1 v=(if (G.dartPair a).1=v then 1 else 0)+(if (G.dartPair a).2=v then 1 else 0) := by
  classical
  rcases a with ⟨e,b⟩
  cases b <;> simp [dartPair,endpointCount,Nat.add_comm]

theorem vertex_sum (c : DirectedSimpleCycle G) (v : V) :
    (∑i:Fin c.length,if c.vertex i=v then (1:ℕ) else 0)=if v∈c.cycleVertices then 1 else 0 := by
  classical
  by_cases hv : v∈c.cycleVertices
  · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hv
    rw [if_pos hv,←hi]
    simp only [c.vertex_injective.eq_iff]
    simp
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hi
    exact hv (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)

theorem selectedDegree_cycleEdges (c : DirectedSimpleCycle G) (v : V) :
    G.selectedDegree c.cycleEdges v=if v∈c.cycleVertices then 2 else 0 := by
  classical
  rw [selectedDegree_eq_sum_endpointCount,cycleEdges,Finset.sum_image (fun _ _ _ _ h=>c.edge_injective h)]
  simp only [endpointCount_dart,c.tail_eq,c.head_eq,Finset.sum_add_distrib,cycleNext_eq_finRotate]
  rw [Equiv.sum_comp (finRotate c.length) (fun i=>if c.vertex i=v then (1:ℕ) else 0),c.vertex_sum]
  split_ifs <;> omega

theorem evenSubgraph (c : DirectedSimpleCycle G) : G.EvenSubgraph c.cycleEdges := by
  intro v
  rw [c.selectedDegree_cycleEdges]
  split_ifs <;> norm_num

end DirectedSimpleCycle
end PlanarHom.MultiGraph
