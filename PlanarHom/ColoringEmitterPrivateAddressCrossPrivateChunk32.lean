import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk32 : List (ℕ×ℕ) := [(1028,1024),(1029,1025),(1030,1026),(1031,1027),(1032,1028),(1033,1029),(1034,1030),(1035,1031),(1036,1032),(1037,1033),(1038,1034),(1039,1035),(1040,1036),(1041,1037),(1042,1038),(1043,1039),(1044,1040),(1045,1041),(1046,1042),(1047,1043),(1048,1044),(1049,1045),(1050,1046),(1051,1047),(1052,1048),(1053,1049),(1054,1050),(1055,1051),(1056,1052),(1057,1053),(1058,1054),(1059,1055)]
theorem crossPrivateChunk32_valid : ∀p∈crossPrivateChunk32,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
