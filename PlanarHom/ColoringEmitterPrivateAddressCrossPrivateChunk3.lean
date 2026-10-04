import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk3 : List (ℕ×ℕ) := [(100,96),(101,97),(102,98),(103,99),(104,100),(105,101),(106,102),(107,103),(108,104),(109,105),(110,106),(111,107),(112,108),(113,109),(114,110),(115,111),(116,112),(117,113),(118,114),(119,115),(120,116),(121,117),(122,118),(123,119),(124,120),(125,121),(126,122),(127,123),(128,124),(129,125),(130,126),(131,127)]
theorem crossPrivateChunk3_valid : ∀p∈crossPrivateChunk3,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
