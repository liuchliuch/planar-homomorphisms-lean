import PlanarHom.ColoringWireMacroRowsErase
import PlanarHom.ColoringCrossMacroRowsErase
import PlanarHom.ColoringFanMacroRowsErase
import PlanarHom.ColoringTestMacroRowsErase
import PlanarHom.ColoringWireMacroRowsCertificate
import PlanarHom.ColoringCrossMacroRowsCertificate
import PlanarHom.ColoringFanMacroRowsCertificate
import PlanarHom.ColoringTestMacroRowsCertificate
import PlanarHom.ColoringEmitterMacroSemantics
import PlanarHom.RotationRowsTransport

/-! Exact local geometric rotations on the canonical graph used by the numeric
emitter. All transports are literal incidence bijections; no LR rotation is
substituted for the fixed coordinate rows. -/
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroRows
open MultiGraph PositiveBlockProgram PlanarityLRRealization
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numericRows (s : CellShape) : RotationRows (LocalPatch.numericGraph s) :=
  match s with
  | .wireTop | .wireBottom | .wireDown =>
    ColoringWireMacroRows.rows.transport ColoringWireMacroEmitterJoin.numericEquiv.symm
  | .cross => ColoringCrossMacroRows.rows.transport ColoringCrossMacroEmitterJoin.numericEquiv.symm
  | .fan => ColoringFanMacroRows.rows.transport ColoringFanMacroEmitterJoin.numericEquiv.symm
  | .test => ColoringTestMacroRows.rows.transport ColoringTestMacroEmitterJoin.numericEquiv.symm

def raw (s : CellShape) (v : LocalPatch.NumericVertex s) : List (ℕ × Bool) :=
  match s with
  | .wireTop | .wireBottom | .wireDown => ColoringWireMacroRows.raw (ColoringWireMacroEmitterJoin.vertexIndex v)
  | .cross => ColoringCrossMacroRows.raw (ColoringCrossMacroEmitterJoin.vertexIndex v)
  | .fan => ColoringFanMacroRows.raw (ColoringFanMacroEmitterJoin.vertexIndex v)
  | .test => ColoringTestMacroRows.raw (ColoringTestMacroEmitterJoin.vertexIndex v)

theorem numericRows_erase (s : CellShape) (v : LocalPatch.NumericVertex s) :
    ((numericRows s).row v).map (fun a=>(a.1.val,a.2))=raw s v := by
  cases s
  all_goals simp only [numericRows,PlanarityLRRealization.RotationRows.transport,List.map_map]
  all_goals first
    | exact ColoringWireMacroRows.erase_row _
    | exact ColoringCrossMacroRows.erase_row _
    | exact ColoringFanMacroRows.erase_row _
    | exact ColoringTestMacroRows.erase_row _

def localRows (s : CellShape) : RotationRows (LocalPatch.graph s) :=
  (numericRows s).transport (MacroSemantics.partsEquiv s).symm

theorem localRows_erase (s : CellShape) (w : LocalPatch.NumericVertex s) :
    ((localRows s).row ((LocalPatch.localVertexParts s).symm w)).map (fun a=>(a.1.val,a.2))=raw s w := by
  simp only [localRows,PlanarityLRRealization.RotationRows.transport,List.map_map]
  simpa only [MultiGraph.IncidenceEquiv.symm,MacroSemantics.partsEquiv,
    MultiGraph.IncidenceEquiv.darts,Equiv.symm_symm,Equiv.apply_symm_apply] using numericRows_erase s w

end PlanarHom.ColoringEmitter.MacroRows
