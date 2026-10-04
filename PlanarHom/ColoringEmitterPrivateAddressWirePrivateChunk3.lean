import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk3 : List (ℕ×ℕ) := [(98,96),(99,97),(100,98),(101,99),(102,100),(103,101),(104,102),(105,103),(106,104),(107,105),(108,106),(109,107),(110,108),(111,109),(112,110),(113,111),(114,112),(115,113),(116,114),(117,115),(118,116),(119,117),(120,118),(121,119),(122,120),(123,121),(124,122),(125,123),(126,124),(127,125),(128,126),(129,127)]
theorem wirePrivateChunk3_valid : ∀p∈wirePrivateChunk3,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
