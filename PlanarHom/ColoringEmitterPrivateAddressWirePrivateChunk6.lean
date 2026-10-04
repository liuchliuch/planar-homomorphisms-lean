import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def wirePrivateChunk6 : List (ℕ×ℕ) := [(194,192),(195,193),(196,194),(197,195),(198,196),(199,197),(200,198),(201,199),(202,200),(203,201),(204,202),(205,203),(206,204),(207,205),(208,206),(209,207),(210,208),(211,209),(212,210),(213,211),(214,212),(215,213),(216,214),(217,215),(218,216),(219,217),(220,218),(221,219),(222,220),(223,221),(224,222),(225,223)]
theorem wirePrivateChunk6_valid : ∀p∈wirePrivateChunk6,address .wire p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
