import PlanarHom.GraphComponentDecomposition

open PlanarHom PlanarHom.Complexity PlanarHom.GraphComponentCode

example : components ⟨0,[],[]⟩ = [] := by decide
example : components ⟨3,[],[]⟩ = [⟨1,[],[]⟩,⟨1,[],[]⟩,⟨1,[],[]⟩] := by decide
example : components ⟨0,[(17,18,9)],[(4,3)]⟩ = [] := by decide
example : components ⟨2,[(17,18,9)],[]⟩ = [⟨1,[],[]⟩,⟨1,[],[]⟩] := by decide

private def loopAndIsolate : MixedCode :=
  ⟨2,[(0,0,1),(0,0,1)],[(0,2),(0,2),(1,0)]⟩

example : parts loopAndIsolate = [[0],[1]] := by decide
example : components loopAndIsolate =
    [⟨1,[(0,0,1),(0,0,1)],[(0,2),(0,2)]⟩,⟨1,[],[(0,0)]⟩] := by decide

private def disconnected : MixedCode :=
  ⟨6,[(0,1,0),(1,1,1),(0,1,0),(3,4,1),(4,3,1)],
    [(4,2),(1,1),(4,2),(2,0)]⟩

private theorem disconnected_valid : disconnected.Valid 2 3 := by
  simp [MixedCode.Valid,disconnected]

example : parts disconnected = [[4,3],[1,0],[5],[2]] := by decide
example : components disconnected =
    [⟨2,[(1,0,1),(0,1,1)],[(0,2),(0,2)]⟩,
     ⟨2,[(1,0,0),(0,0,1),(1,0,0)],[(0,1)]⟩,
     ⟨1,[],[]⟩,⟨1,[],[(0,0)]⟩] := by decide

example : ∀c∈components disconnected,c.Valid 2 3 ∧ (support c).Connected := by
  intro c hc
  exact ⟨components_valid disconnected disconnected_valid c hc,
    components_connected disconnected disconnected_valid c hc⟩

example : ((components disconnected).map MixedCode.vertices).sum=6 :=
  components_vertex_sum disconnected

example : Together (parts disconnected) 0 1 := by unfold Together; decide
example : ¬ Together (parts disconnected) 0 4 := by unfold Together; decide
example : Reach disconnected.edges 0 1 :=
  (together_iff_reach disconnected disconnected_valid 0 1 (by decide)).mp (by unfold Together; decide)
example : ¬ Reach disconnected.edges 0 4 := by
  intro h
  exact (show ¬Together (parts disconnected) 0 4 by unfold Together; decide)
    ((together_iff_reach disconnected disconnected_valid 0 4 (by decide)).mpr h)
