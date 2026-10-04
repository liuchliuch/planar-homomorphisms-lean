import PlanarHom.ColoringCrossMacroTyped
import PlanarHom.ColoringEmitterLocalPatches
import PlanarHom.ColoringIncidenceTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringCrossMacroEmitterJoin
open MultiGraph PositiveBlockProgram ColoringEmitter
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev shape : CellShape := .cross

theorem edges_eq : Macro.edges .cross=List.ofFn
    (fun e : ColoringCrossMacroCoordinates.Edge =>
      ((ColoringCrossMacroCoordinates.graph.src e).val,(ColoringCrossMacroCoordinates.graph.dst e).val)) := by
  decide +kernel

def edgeIndex : LocalPatch.Edge shape ≃ ColoringCrossMacroCoordinates.Edge := finCongr (by decide)
def vertexIndex : LocalPatch.NumericVertex shape ≃ ColoringCrossMacroCoordinates.Vertex := finCongr (by decide)

theorem edgePair_eq (e : LocalPatch.Edge shape) : LocalPatch.edgePair shape e=
    ((ColoringCrossMacroCoordinates.graph.src (edgeIndex e)).val,
     (ColoringCrossMacroCoordinates.graph.dst (edgeIndex e)).val) := by
  dsimp [LocalPatch.edgePair]
  simp only [show shape.kind=Kind.cross from rfl]
  simp only [List.get_eq_getElem,edges_eq,List.getElem_ofFn]
  rfl

def numericEquiv : IncidenceEquiv (LocalPatch.numericGraph shape) ColoringCrossMacroCoordinates.graph where
  vertex := vertexIndex
  edge := edgeIndex
  src_eq e := by
    apply Fin.ext
    exact (congrArg Prod.fst (edgePair_eq e)).symm
  dst_eq e := by
    apply Fin.ext
    exact (congrArg Prod.snd (edgePair_eq e)).symm

theorem port_eq : ∀p : LocalPatch.Port shape,
    vertexIndex (LocalPatch.portVertex shape p)=ColoringCrossMacroTyped.boundaryIds p.1 p.2 := by
  decide +kernel

end PlanarHom.ColoringCrossMacroEmitterJoin
