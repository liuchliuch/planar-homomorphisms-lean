import PlanarHom.OccurrenceAlternatingWordPartition

/-! NEW unrestricted occurrence-cycle sign ratio, including parallel two-cycles. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [LinearOrder V]

theorem CycleFlipWordData.sign_ratio {G : MultiGraph V E} {M N : Finset E}
    (c : CycleFlipWordData G M N) (orientation : E → Bool) :
    G.matchingPfaffianSign (R := ℤ) orientation M =
      G.matchingPfaffianSign orientation N * (-boundarySign orientation (c.left ++ c.right)) := by
  have hw := orientedPairSign_rotate_word (c.left.map G.dartPair) (c.right.map G.dartPair)
    (c.common.map G.dartPair) c.first c.rest c.left_word c.right_word
    (by simpa [dartWord] using c.left_nodup)
  have hleft := G.matchingPfaffianSign_eq_word orientation _ c.left_nodup
  have hright := G.matchingPfaffianSign_eq_word orientation _ c.right_nodup
  rw [c.left_edges] at hleft
  rw [c.right_edges] at hright
  rw [hleft,hright]
  simp only [dartWord,List.map_append,wordSign_pairWord,boundarySign_append]
  rw [hw]
  have hr := boundarySign_sq orientation c.right
  calc
    _ = -(orientedPairSign (List.map G.dartPair c.right ++ List.map G.dartPair c.common)) *
          boundarySign orientation c.left * boundarySign orientation c.common *
          (boundarySign orientation c.right)^2 := by rw [hr]; ring
    _ = _ := by ring

theorem AlternatingCycleFlip.matchingPfaffianSign_ratio {G : MultiGraph V E} {M N : Finset E}
    (c : AlternatingCycleFlip G M N) (orientation : E → Bool) :
    G.matchingPfaffianSign (R := ℤ) orientation M =
      G.matchingPfaffianSign orientation N * (-boundarySign orientation c.cycle.cycleDarts) := by
  rw [← boundarySign_perm orientation c.wordPartition_cycle_perm]
  exact c.wordPartition.sign_ratio orientation

end PlanarHom.MultiGraph
