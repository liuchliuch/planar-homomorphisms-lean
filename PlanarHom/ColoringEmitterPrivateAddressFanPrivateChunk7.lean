import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk7 : List (ℕ×ℕ) := [(227,224),(228,225),(229,226),(230,227),(231,228),(232,229),(233,230),(234,231),(235,232),(236,233),(237,234),(238,235),(239,236),(240,237),(241,238),(242,239),(243,240),(244,241),(245,242),(246,243),(247,244),(248,245),(249,246),(250,247),(251,248),(252,249),(253,250),(254,251),(255,252),(256,253),(257,254),(258,255)]
theorem fanPrivateChunk7_valid : ∀p∈fanPrivateChunk7,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
