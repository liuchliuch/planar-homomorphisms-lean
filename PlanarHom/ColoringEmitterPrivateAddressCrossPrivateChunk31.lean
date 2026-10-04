import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk31 : List (ℕ×ℕ) := [(996,992),(997,993),(998,994),(999,995),(1000,996),(1001,997),(1002,998),(1003,999),(1004,1000),(1005,1001),(1006,1002),(1007,1003),(1008,1004),(1009,1005),(1010,1006),(1011,1007),(1012,1008),(1013,1009),(1014,1010),(1015,1011),(1016,1012),(1017,1013),(1018,1014),(1019,1015),(1020,1016),(1021,1017),(1022,1018),(1023,1019),(1024,1020),(1025,1021),(1026,1022),(1027,1023)]
theorem crossPrivateChunk31_valid : ∀p∈crossPrivateChunk31,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
