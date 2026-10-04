import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk34 : List (ℕ×ℕ) := [(1092,1088),(1093,1089),(1094,1090),(1095,1091),(1096,1092),(1097,1093),(1098,1094),(1099,1095),(1100,1096),(1101,1097),(1102,1098),(1103,1099),(1104,1100),(1105,1101),(1106,1102),(1107,1103),(1108,1104),(1109,1105),(1110,1106),(1111,1107),(1112,1108),(1113,1109),(1114,1110),(1115,1111),(1116,1112),(1117,1113),(1118,1114),(1119,1115),(1120,1116),(1121,1117),(1122,1118),(1123,1119)]
theorem crossPrivateChunk34_valid : ∀p∈crossPrivateChunk34,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
