import PlanarHom.SurfaceCycleBoundaryFamily
import PlanarHom.OccurrenceMatchingCycleConnectivity

/-! NEW exact disjoint occurrence-cycle decomposition data. -/
noncomputable section
open Classical
open scoped symmDiff
namespace PlanarHom.MultiGraph
variable {V E : Type*} [Fintype V] [Fintype E]

structure MatchingCycleDecomposition (G : MultiGraph V E) (M N : Finset E) (n : ℕ) where
  family : CycleBoundaryFamily G (M ∆ N) n
  even_length : ∀ i, Even (family.cycle i).length
  original_left_even : ∀ i j, ((family.cycle i).dart j).1 ∈ M ↔ Even j.val
  original_right_odd : ∀ i j, ((family.cycle i).dart j).1 ∈ N ↔ Odd j.val
  states : Fin (n+1) → Finset E
  states_first : states 0 = M
  states_last : states (Fin.last n) = N
  flips : ∀ i : Fin n, AlternatingCycleFlip G (states i.castSucc) (states i.succ)
  flip_cycle : ∀ i, (flips i).cycle = family.cycle i

namespace PerfectMatching
variable {G : MultiGraph V E} {M N : Finset E}
variable (c : DirectedSimpleCycle G)
variable (hleft : ∀ i, (c.dart i).1 ∈ M ↔ Even i.val)
variable (hright : ∀ i, (c.dart i).1 ∈ N ↔ Odd i.val)

include hleft hright in
theorem cycle_mem_symmDiff {e : E} (he : e ∈ c.cycleEdges) : e ∈ M ∆ N := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  simp only [Finset.mem_symmDiff, hleft, hright, Nat.even_iff, Nat.odd_iff]
  omega

theorem patchCycle_mem_on {e : E} (he : e ∈ c.cycleEdges) :
    e ∈ patchCycle (M:=M) (N:=N) c ↔ e ∈ N := by
  simp [patchCycle,he]

theorem patchCycle_mem_off {e : E} (he : e ∉ c.cycleEdges) :
    e ∈ patchCycle (M:=M) (N:=N) c ↔ e ∈ M := by
  simp [patchCycle,he]

theorem patchCycle_symmDiff :
    patchCycle (M:=M) (N:=N) c ∆ N = (M ∆ N) \ c.cycleEdges := by
  ext e
  by_cases he : e ∈ c.cycleEdges <;> simp [Finset.mem_symmDiff,patchCycle,he]

variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (heven : Even c.length)
include hM hN heven hleft hright in
theorem patchCycle_difference_not_incident {v : V} (hv : v ∈ c.cycleVertices)
    {e : E} (he : e ∈ patchCycle (M:=M) (N:=N) c ∆ N) :
    ¬ 0 < G.endpointCount e v := by
  intro hev
  rw [patchCycle_symmDiff] at he
  have hd := Finset.mem_sdiff.mp he
  have hmem : e ∈ M ∨ e ∈ N := by
    simpa only [Finset.mem_union] using (Finset.symmDiff_subset_union hd.1)
  apply hd.2
  rcases hmem with hm | hn
  · exact c.matching_incident_confined M hM (c.even_coverage heven M hleft) v hv e hm hev
  · exact c.matching_incident_confined N hN (c.odd_coverage heven N hright) v hv e hn hev

end PerfectMatching
end PlanarHom.MultiGraph
