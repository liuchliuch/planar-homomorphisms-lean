import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk26 : List (ℕ×ℕ) := [(836,832),(837,833),(838,834),(839,835),(840,836),(841,837),(842,838),(843,839),(844,840),(845,841),(846,842),(847,843),(848,844),(849,845),(850,846),(851,847),(852,848),(853,849),(854,850),(855,851),(856,852),(857,853),(858,854),(859,855),(860,856),(861,857),(862,858),(863,859),(864,860),(865,861),(866,862),(867,863)]
theorem crossPrivateChunk26_valid : ∀p∈crossPrivateChunk26,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
