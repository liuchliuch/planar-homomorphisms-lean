import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk7 : List (ℕ×ℕ) := [(226,224),(227,225),(228,226),(229,227),(230,228),(231,229),(232,230),(233,231),(234,232),(235,233),(236,234),(237,235),(238,236),(239,237),(240,238),(241,239),(242,240),(243,241),(244,242),(245,243),(246,244),(247,245),(248,246),(249,247),(250,248),(251,249),(252,250),(253,251),(254,252),(255,253),(256,254),(257,255)]
theorem wirePrivateChunk7_valid : ∀p∈wirePrivateChunk7,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
