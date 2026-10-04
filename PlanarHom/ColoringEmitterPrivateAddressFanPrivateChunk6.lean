import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk6 : List (ℕ×ℕ) := [(195,192),(196,193),(197,194),(198,195),(199,196),(200,197),(201,198),(202,199),(203,200),(204,201),(205,202),(206,203),(207,204),(208,205),(209,206),(210,207),(211,208),(212,209),(213,210),(214,211),(215,212),(216,213),(217,214),(218,215),(219,216),(220,217),(221,218),(222,219),(223,220),(224,221),(225,222),(226,223)]
theorem fanPrivateChunk6_valid : ∀p∈fanPrivateChunk6,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
