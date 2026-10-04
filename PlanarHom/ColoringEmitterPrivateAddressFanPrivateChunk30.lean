import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk30 : List (ℕ×ℕ) := [(963,960),(964,961),(965,962),(966,963),(967,964),(968,965),(969,966),(970,967),(971,968),(972,969),(973,970),(974,971),(975,972),(976,973),(977,974),(978,975),(979,976),(980,977),(981,978),(982,979),(983,980),(984,981),(985,982),(986,983),(987,984),(988,985),(989,986),(990,987),(991,988),(992,989),(993,990),(994,991)]
theorem fanPrivateChunk30_valid : ∀p∈fanPrivateChunk30,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
