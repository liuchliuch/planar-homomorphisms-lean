import PlanarHom.IndexedRotationCertificate
import PlanarHom.ColoringMacroCrossFramedFaces
import PlanarHom.ColoringMacroCrossFramedRotationCheckHostbound
import PlanarHom.ColoringMacroCrossFramedRotationCheckVertexrootbound
import PlanarHom.ColoringMacroCrossFramedRotationCheckParentbound
import PlanarHom.ColoringMacroCrossFramedRotationCheckParentedgebound
import PlanarHom.ColoringMacroCrossFramedRotationCheckVertexRootHost
import PlanarHom.ColoringMacroCrossFramedRotationCheckVertexStepHost
import PlanarHom.ColoringMacroCrossFramedRotationCheckVertexZeroRoot
import PlanarHom.ColoringMacroCrossFramedRotationCheckVertexStepRank
import PlanarHom.ColoringMacroCrossFramedRotationCheckConnectZeroRoot
import PlanarHom.ColoringMacroCrossFramedRotationCheckConnectStepRank
import PlanarHom.ColoringMacroCrossFramedRotationCheckConnectAdjacent

namespace PlanarHom.ColoringMacroFaces.CrossFramed
open MultiGraph FinitePermutationCycles RadialPotts.Assembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def host (i : Fin 6336) : Fin 1274 := ⟨hostValue i.val,hostBound i⟩
def vertexRoot (v : Fin 1274) : Fin 6336 := ⟨vertexRootValue v.val,vertexRootBound v⟩
def vertexRank (d : Fin 6336) : ℕ := vertexRankValue d.val
theorem rotation_value (d : Fin 6336) : ((permutation*IndexedRotationCertificate.flip 3168) d).val=rotateValue d.val := by
  change nextValue (IndexedRotationCertificate.flip 3168 d).val=rotateValue d.val
  rw [IndexedRotationCertificate.flip_value]
  rfl
def rotationCertificate : LabelCertificate (permutation*IndexedRotationCertificate.flip 3168) (Fin 1274) where
  label := host
  root := vertexRoot
  rank := vertexRank
  root_label v := Fin.ext (vertex_root_host v)
  step_label d := Fin.ext (by
    change hostValue ((permutation*IndexedRotationCertificate.flip 3168) d).val=hostValue d.val
    rw [rotation_value]
    exact vertex_step_host d)
  zero_root d h := Fin.ext (vertex_zero_root d h)
  step_rank d h := by
    change vertexRankValue ((permutation*IndexedRotationCertificate.flip 3168) d).val+1=vertexRankValue d.val
    rw [rotation_value]
    exact vertex_step_rank d h
def framedGraph : MultiGraph (Fin 1274) (Fin 3168) := IndexedRotationCertificate.graph host
def framedRotation : Equiv.Perm (Medial.Dart (Fin 3168)) := IndexedRotationCertificate.rotation permutation
theorem framedRotation_cycles (a b : Medial.Dart (Fin 3168)) : framedRotation.SameCycle a b ↔ framedGraph.dartVertex a=framedGraph.dartVertex b :=
  IndexedRotationCertificate.rotation_cycles (n:=1274) (m:=3168) host permutation rotationCertificate rfl a b
theorem framedGraph_noIsolates : Function.Surjective framedGraph.dartVertex :=
  IndexedRotationCertificate.graph_host_surjective (n:=1274) (m:=3168) host permutation rotationCertificate rfl
def connectivityCertificate : IndexedRotationCertificate.ConnectivityCertificate framedGraph where
  root := 0
  parent v := ⟨parentValue v.val,parentBound v⟩
  parentEdge v := ⟨parentEdgeValue v.val,parentEdgeBound v⟩
  rank v := connectRankValue v.val
  zero_root v h := Fin.ext (connect_zero_root v h)
  decreases v h := connect_step_rank v h
  adjacent v h := by
    have hh := connect_adjacent v h
    rcases hh with ⟨hs,ht⟩ | ⟨ht,hs⟩
    · left
      constructor
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=3168)]; simpa [dartIndex] using hs
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=3168)]; simpa [dartIndex] using ht
    · right
      constructor
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=3168)]; simpa [dartIndex] using ht
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=3168)]; simpa [dartIndex] using hs
theorem framedGraph_connected (a b : Fin 1274) : framedGraph.componentSetoid Finset.univ a b :=
  connectivityCertificate.connected a b
end PlanarHom.ColoringMacroFaces.CrossFramed
