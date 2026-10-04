import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk32 : List (ℕ×ℕ) := [(1027,1024),(1028,1025),(1029,1026),(1030,1027),(1031,1028),(1032,1029),(1039,1030),(1040,1031),(1041,1032),(1042,1033),(1043,1034),(1044,1035),(1045,1036),(1046,1037),(1047,1038),(1048,1039),(1049,1040),(1050,1041),(1051,1042),(1052,1043),(1053,1044)]
theorem fanPrivateChunk32_valid : ∀p∈fanPrivateChunk32,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
