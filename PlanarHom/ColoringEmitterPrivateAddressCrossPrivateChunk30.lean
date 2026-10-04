import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk30 : List (ℕ×ℕ) := [(964,960),(965,961),(966,962),(967,963),(968,964),(969,965),(970,966),(971,967),(972,968),(973,969),(974,970),(975,971),(976,972),(977,973),(978,974),(979,975),(980,976),(981,977),(982,978),(983,979),(984,980),(985,981),(986,982),(987,983),(988,984),(989,985),(990,986),(991,987),(992,988),(993,989),(994,990),(995,991)]
theorem crossPrivateChunk30_valid : ∀p∈crossPrivateChunk30,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
