import PlanarHom.ColoringFanMacroTyped
import PlanarHom.ColoringEmitterLocalPatches
import PlanarHom.ColoringIncidenceTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringFanMacroEmitterJoin
open MultiGraph PositiveBlockProgram ColoringEmitter
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev shape : CellShape := .fan

theorem edges_eq : Macro.edges .fan=List.ofFn
    (fun e : ColoringFanMacroCoordinates.Edge =>
      ((ColoringFanMacroCoordinates.graph.src e).val,(ColoringFanMacroCoordinates.graph.dst e).val)) := by
  decide +kernel

def edgeIndex : LocalPatch.Edge shape ≃ ColoringFanMacroCoordinates.Edge := finCongr (by decide)
def vertexIndex : LocalPatch.NumericVertex shape ≃ ColoringFanMacroCoordinates.Vertex := finCongr (by decide)

theorem edgePair_eq (e : LocalPatch.Edge shape) : LocalPatch.edgePair shape e=
    ((ColoringFanMacroCoordinates.graph.src (edgeIndex e)).val,
     (ColoringFanMacroCoordinates.graph.dst (edgeIndex e)).val) := by
  dsimp [LocalPatch.edgePair]
  simp only [show shape.kind=Kind.fan from rfl]
  simp only [List.get_eq_getElem,edges_eq,List.getElem_ofFn]
  rfl

def numericEquiv : IncidenceEquiv (LocalPatch.numericGraph shape) ColoringFanMacroCoordinates.graph where
  vertex := vertexIndex
  edge := edgeIndex
  src_eq e := by
    apply Fin.ext
    exact (congrArg Prod.fst (edgePair_eq e)).symm
  dst_eq e := by
    apply Fin.ext
    exact (congrArg Prod.snd (edgePair_eq e)).symm

theorem port_eq : ∀p : LocalPatch.Port shape,
    vertexIndex (LocalPatch.portVertex shape p)=ColoringFanMacroTyped.boundaryIds p.1 p.2 := by
  decide +kernel

end PlanarHom.ColoringFanMacroEmitterJoin
