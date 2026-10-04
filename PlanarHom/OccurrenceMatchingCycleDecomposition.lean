import PlanarHom.OccurrenceMatchingCycleDecompositionData

/-! NEW disjoint cycle decomposition, constructed by strictly decreasing
occurrence disagreement. Every recursive cycle avoids all preceding vertices. -/
noncomputable section
open Classical
open scoped symmDiff
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
def AlternatingCycleFlip.reindex {M N M' N' : Finset E}
    (c : AlternatingCycleFlip G M N) (hm : M=M') (hn : N=N') :
    AlternatingCycleFlip G M' N' where
  cycle := c.cycle
  even_length := c.even_length
  left_perfect := hm ▸ c.left_perfect
  right_perfect := hn ▸ c.right_perfect
  left_even := hm ▸ c.left_even
  right_odd := hn ▸ c.right_odd
  agree_off := hm ▸ hn ▸ c.agree_off

namespace MatchingCycleDecomposition

def refl (M : Finset E) : MatchingCycleDecomposition G M M 0 where
  family := {
    cycle := fun i => Fin.elim0 i
    vertex_disjoint := fun i => Fin.elim0 i
    edge_cover := by intro e; simp }
  even_length := fun i => Fin.elim0 i
  original_left_even := fun i => Fin.elim0 i
  original_right_odd := fun i => Fin.elim0 i
  states := fun _ => M
  states_first := rfl
  states_last := rfl
  flips := fun i => Fin.elim0 i
  flip_cycle := fun i => Fin.elim0 i

variable {M N : Finset E} {n : ℕ}
variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
variable (c : DirectedSimpleCycle G) (heven : Even c.length)
variable (hleft : ∀i,(c.dart i).1∈M ↔ Even i.val)
variable (hright : ∀i,(c.dart i).1∈N ↔ Odd i.val)
variable (d : MatchingCycleDecomposition G (PerfectMatching.patchCycle (M:=M) (N:=N) c) N n)

include hM hN heven hleft hright in
theorem head_vertex_disjoint (i : Fin n) : Disjoint c.cycleVertices (d.family.cycle i).cycleVertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hc
  have he := d.family.cycle_dart_mem i j
  apply PerfectMatching.patchCycle_difference_not_incident c hleft hright hM hN heven hv he
  rw [DirectedSimpleCycle.endpointCount_dart,(d.family.cycle i).tail_eq,hj]
  simp

include hM hN heven hleft hright in
theorem tail_edge_not_head (i : Fin n) (j : Fin (d.family.cycle i).length) :
    ((d.family.cycle i).dart j).1 ∉ c.cycleEdges := by
  have he := d.family.cycle_dart_mem i j
  have hx := Finset.mem_sdiff.mp ((congrArg (fun S : Finset E => ((d.family.cycle i).dart j).1 ∈ S) (PerfectMatching.patchCycle_symmDiff (M:=M) (N:=N) c)).mp he)
  exact hx.2

def cons : MatchingCycleDecomposition G M N (n+1) where
  family := {
    cycle := Fin.cons c d.family.cycle
    vertex_disjoint := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact head_vertex_disjoint hM hN c heven hleft hright d j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (head_vertex_disjoint hM hN c heven hleft hright d i).symm
        | succ j => exact d.family.vertex_disjoint i j (fun h => hij (congrArg Fin.succ h))
    edge_cover := by
      intro e
      constructor
      · intro he
        by_cases hc : e∈c.cycleEdges
        · exact ⟨0,hc⟩
        · have hp : e∈PerfectMatching.patchCycle (M:=M) (N:=N) c ∆ N := by
            rw [PerfectMatching.patchCycle_symmDiff]
            exact Finset.mem_sdiff.mpr ⟨he,hc⟩
          obtain ⟨i,hi⟩ := (d.family.edge_cover e).mp hp
          exact ⟨i.succ,hi⟩
      · rintro ⟨i,hi⟩
        cases i using Fin.cases with
        | zero => exact PerfectMatching.cycle_mem_symmDiff c hleft hright hi
        | succ i =>
          have he := (d.family.edge_cover e).mpr ⟨i,hi⟩
          rw [PerfectMatching.patchCycle_symmDiff] at he
          exact (Finset.mem_sdiff.mp he).1 }
  even_length := Fin.cases heven d.even_length
  original_left_even := by
    intro i
    cases i using Fin.cases with
    | zero => exact hleft
    | succ i =>
      intro j
      have he := tail_edge_not_head hM hN c heven hleft hright d i j
      exact (PerfectMatching.patchCycle_mem_off c he).symm.trans (d.original_left_even i j)
  original_right_odd := Fin.cases hright d.original_right_odd
  states := Fin.cons M d.states
  states_first := rfl
  states_last := d.states_last
  flips := Fin.cases
    ((hM.patchCycle_flip hN c heven hleft hright).reindex rfl d.states_first.symm)
    (fun i => (d.flips i).reindex rfl rfl)
  flip_cycle := Fin.cases rfl d.flip_cycle

end MatchingCycleDecomposition

namespace PerfectMatching

theorem exists_cycleDecomposition {M N : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) :
    ∃n,Nonempty (MatchingCycleDecomposition G M N n) := by
  suffices ∀k,∀M:Finset E,(M\N).card=k→G.PerfectMatching M→
      ∃n,Nonempty (MatchingCycleDecomposition G M N n) from this _ M rfl hM
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro M hsize hM
      by_cases he:M=N
      · subst M
        exact ⟨0,⟨MatchingCycleDecomposition.refl N⟩⟩
      · obtain ⟨c,heven,hleft,hright⟩:=hM.exists_alternating_cycle hN he
        let P:=patchCycle (M:=M) (N:=N) c
        have hP:G.PerfectMatching P:=hM.patchCycle_perfect hN c heven hleft hright
        have hlt:(P\N).card<k:=by
          have hh:=patchCycle_difference_card_lt c hleft hright
          change (P\N).card<(M\N).card at hh
          omega
        obtain ⟨n,⟨d⟩⟩ := ih (P\N).card hlt P rfl hP
        exact ⟨n+1,⟨d.cons hM hN c heven hleft hright⟩⟩

end PerfectMatching
end PlanarHom.MultiGraph
