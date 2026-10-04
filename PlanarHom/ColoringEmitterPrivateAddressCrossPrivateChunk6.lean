import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk6 : List (ℕ×ℕ) := [(196,192),(197,193),(198,194),(199,195),(200,196),(201,197),(202,198),(203,199),(204,200),(205,201),(206,202),(207,203),(208,204),(209,205),(210,206),(211,207),(212,208),(213,209),(214,210),(215,211),(216,212),(217,213),(218,214),(219,215),(220,216),(221,217),(222,218),(223,219),(224,220),(225,221),(226,222),(227,223)]
theorem crossPrivateChunk6_valid : ∀p∈crossPrivateChunk6,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
