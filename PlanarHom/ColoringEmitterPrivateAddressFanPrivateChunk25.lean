import PlanarHom.ColoringEmitterMacroValidity

/-! NEW bounded kernel checks for private address tables. Each independent
check covers at most 32 entries; the global statement is proved by list gluing. -/
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def fanPrivateChunk25 : List (ℕ×ℕ) := [(803,800),(804,801),(805,802),(806,803),(807,804),(808,805),(809,806),(810,807),(811,808),(812,809),(813,810),(814,811),(815,812),(816,813),(817,814),(818,815),(819,816),(820,817),(821,818),(822,819),(823,820),(824,821),(825,822),(826,823),(827,824),(828,825),(829,826),(830,827),(831,828),(832,829),(833,830),(834,831)]
theorem fanPrivateChunk25_valid : ∀p∈fanPrivateChunk25,address .fan p.1=(2,p.2,0) := by decide +kernel

end PlanarHom.ColoringEmitter.Macro
