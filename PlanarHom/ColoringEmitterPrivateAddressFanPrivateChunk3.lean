import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk3 : List (ℕ×ℕ) := [(99,96),(100,97),(101,98),(102,99),(103,100),(104,101),(105,102),(106,103),(107,104),(108,105),(109,106),(110,107),(111,108),(112,109),(113,110),(114,111),(115,112),(116,113),(117,114),(118,115),(119,116),(120,117),(121,118),(122,119),(123,120),(124,121),(125,122),(126,123),(127,124),(128,125),(129,126),(130,127)]
theorem fanPrivateChunk3_valid : ∀p∈fanPrivateChunk3,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
