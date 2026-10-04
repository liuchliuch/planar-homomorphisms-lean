import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk7 : List (ℕ×ℕ) := [(228,224),(229,225),(230,226),(231,227),(232,228),(233,229),(234,230),(235,231),(236,232),(237,233),(238,234),(239,235),(240,236),(241,237),(242,238),(243,239),(244,240),(245,241),(246,242),(247,243),(248,244),(249,245),(250,246),(251,247),(252,248),(253,249),(254,250),(255,251),(256,252),(257,253),(258,254),(259,255)]
theorem crossPrivateChunk7_valid : ∀p∈crossPrivateChunk7,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
