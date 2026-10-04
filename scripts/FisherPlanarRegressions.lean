import PlanarHom.FisherPlanarReduction
import PlanarHom.RootedLoop

noncomputable section
open Classical unitInterval
namespace PlanarHom.FisherPlanarRegressions
open MultiGraph Fisher

def collinearPorts : Fin 3 → Plane := ![(-1,1), (0,1), (1,1)]

/-- Three ports on one flat face of the product-norm sphere require the
curved branch. Its midpoint is strictly inside the ball, away from the path. -/
example : triangleClosing collinearPorts (0,0) ⟨1/2, by constructor <;> norm_num⟩ = (0,1/2) := by
  have hp0 : collinearPorts 0 = (-1,1) := rfl
  have hp1 : collinearPorts 1 = (0,1) := rfl
  have hp2 : collinearPorts 2 = (1,1) := rfl
  have h : signedSide (collinearPorts 0) (collinearPorts 2) (collinearPorts 1) = 0 := by
    rw [hp0,hp1,hp2]
    norm_num [signedSide]
  rw [triangleClosing, if_pos h]
  rw [hp0,hp2]
  apply Prod.ext <;> norm_num [bezierCurve]

/-- The genuine planar source-loop case, with negative even-subgraph weight. -/
example : ∃ o : RootedGraph.singleLoop.IncidenceOrdering,
    (fisherGraph o).Planar ∧
      (fisherGraph o).perfectMatchingSum (fisherWeight o (fun _ => -(1/2 : ℝ))) = 2 := by
  obtain ⟨o,hp,h⟩ := exists_planar_ising_matching RootedGraph.singleLoop_planar 3 (by norm_num)
  refine ⟨o,hp,?_⟩
  norm_num [RootedGraph.singleLoop, MultiGraph.partition, MultiGraph.assignmentWeight, Boolean.W] at h
  exact h.symm

/-- Every ordinary planar input has a single constructed graph that works
simultaneously for every signed weight assignment. -/
example {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E} (hG : G.Planar) :
    ∃ o : G.IncidenceOrdering, (fisherGraph o).Planar ∧
      (fisherGraph o).perfectMatchingSum (fisherWeight o (fun _ => 0)) =
        (4 : ℝ) ^ Fintype.card V := by
  obtain ⟨o,hp,hw⟩ := exists_planar_fisher hG
  exact ⟨o,hp,by simpa only [evenSubgraphSum_zero, mul_one] using hw (fun _ => 0)⟩

end PlanarHom.FisherPlanarRegressions
