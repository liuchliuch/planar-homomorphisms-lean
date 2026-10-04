import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk31 : List (ℕ×ℕ) := [(995,992),(996,993),(997,994),(998,995),(999,996),(1000,997),(1001,998),(1002,999),(1003,1000),(1004,1001),(1005,1002),(1006,1003),(1007,1004),(1008,1005),(1009,1006),(1010,1007),(1011,1008),(1012,1009),(1013,1010),(1014,1011),(1015,1012),(1016,1013),(1017,1014),(1018,1015),(1019,1016),(1020,1017),(1021,1018),(1022,1019),(1023,1020),(1024,1021),(1025,1022),(1026,1023)]
theorem fanPrivateChunk31_valid : ∀p∈fanPrivateChunk31,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
