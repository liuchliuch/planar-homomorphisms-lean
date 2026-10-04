import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def crossPrivateChunk25 : List (ℕ×ℕ) := [(804,800),(805,801),(806,802),(807,803),(808,804),(809,805),(810,806),(811,807),(812,808),(813,809),(814,810),(815,811),(816,812),(817,813),(818,814),(819,815),(820,816),(821,817),(822,818),(823,819),(824,820),(825,821),(826,822),(827,823),(828,824),(829,825),(830,826),(831,827),(832,828),(833,829),(834,830),(835,831)]
theorem crossPrivateChunk25_valid : ∀p∈crossPrivateChunk25,address .cross p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
