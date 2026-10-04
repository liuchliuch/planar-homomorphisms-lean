import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk26 : List (ℕ×ℕ) := [(835,832),(836,833),(837,834),(838,835),(839,836),(840,837),(841,838),(842,839),(843,840),(844,841),(845,842),(846,843),(847,844),(848,845),(849,846),(850,847),(851,848),(852,849),(853,850),(854,851),(855,852),(856,853),(857,854),(858,855),(859,856),(860,857),(861,858),(862,859),(863,860),(864,861),(865,862),(866,863)]
theorem fanPrivateChunk26_valid : ∀p∈fanPrivateChunk26,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
