import PlanarHom.IndexedRotationCertificate
import PlanarHom.ColoringMacroWireFramedFaces
import PlanarHom.ColoringMacroWireFramedRotationCheckHostbound
import PlanarHom.ColoringMacroWireFramedRotationCheckVertexrootbound
import PlanarHom.ColoringMacroWireFramedRotationCheckParentbound
import PlanarHom.ColoringMacroWireFramedRotationCheckParentedgebound
import PlanarHom.ColoringMacroWireFramedRotationCheckVertexRootHost
import PlanarHom.ColoringMacroWireFramedRotationCheckVertexStepHost
import PlanarHom.ColoringMacroWireFramedRotationCheckVertexZeroRoot
import PlanarHom.ColoringMacroWireFramedRotationCheckVertexStepRank
import PlanarHom.ColoringMacroWireFramedRotationCheckConnectZeroRoot
import PlanarHom.ColoringMacroWireFramedRotationCheckConnectStepRank
import PlanarHom.ColoringMacroWireFramedRotationCheckConnectAdjacent

namespace PlanarHom.ColoringMacroFaces.WireFramed
open MultiGraph FinitePermutationCycles RadialPotts.Assembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def host (i : Fin 2646) : Fin 534 := ⟨hostValue i.val,hostBound i⟩
def vertexRoot (v : Fin 534) : Fin 2646 := ⟨vertexRootValue v.val,vertexRootBound v⟩
def vertexRank (d : Fin 2646) : ℕ := vertexRankValue d.val
theorem rotation_value (d : Fin 2646) : ((permutation*IndexedRotationCertificate.flip 1323) d).val=rotateValue d.val := by
  change nextValue (IndexedRotationCertificate.flip 1323 d).val=rotateValue d.val
  rw [IndexedRotationCertificate.flip_value]
  rfl
def rotationCertificate : LabelCertificate (permutation*IndexedRotationCertificate.flip 1323) (Fin 534) where
  label := host
  root := vertexRoot
  rank := vertexRank
  root_label v := Fin.ext (vertex_root_host v)
  step_label d := Fin.ext (by
    change hostValue ((permutation*IndexedRotationCertificate.flip 1323) d).val=hostValue d.val
    rw [rotation_value]
    exact vertex_step_host d)
  zero_root d h := Fin.ext (vertex_zero_root d h)
  step_rank d h := by
    change vertexRankValue ((permutation*IndexedRotationCertificate.flip 1323) d).val+1=vertexRankValue d.val
    rw [rotation_value]
    exact vertex_step_rank d h
def framedGraph : MultiGraph (Fin 534) (Fin 1323) := IndexedRotationCertificate.graph host
def framedRotation : Equiv.Perm (Medial.Dart (Fin 1323)) := IndexedRotationCertificate.rotation permutation
theorem framedRotation_cycles (a b : Medial.Dart (Fin 1323)) : framedRotation.SameCycle a b ↔ framedGraph.dartVertex a=framedGraph.dartVertex b :=
  IndexedRotationCertificate.rotation_cycles (n:=534) (m:=1323) host permutation rotationCertificate rfl a b
theorem framedGraph_noIsolates : Function.Surjective framedGraph.dartVertex :=
  IndexedRotationCertificate.graph_host_surjective (n:=534) (m:=1323) host permutation rotationCertificate rfl
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
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=1323)]; simpa [dartIndex] using hs
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=1323)]; simpa [dartIndex] using ht
    · right
      constructor
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=1323)]; simpa [dartIndex] using ht
      · apply Fin.ext; simp only [framedGraph,IndexedRotationCertificate.graph,host]; rw [dartIndexEquiv_val (m:=1323)]; simpa [dartIndex] using hs
theorem framedGraph_connected (a b : Fin 534) : framedGraph.componentSetoid Finset.univ a b :=
  connectivityCertificate.connected a b
end PlanarHom.ColoringMacroFaces.WireFramed
