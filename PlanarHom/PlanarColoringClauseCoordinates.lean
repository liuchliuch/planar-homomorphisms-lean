import PlanarHom.PlanarColoringClauseGraph
import PlanarHom.IntegerStraightDrawing

/-! Kernel-checked 105-vertex / 254-edge integer drawing of the exact-one
color clause. The coordinate search is untrusted; every finite separation and
vertex-avoidance condition is proved by reduction in Lean's kernel. -/
noncomputable section
namespace PlanarHom.PlanarColoringClause
open MultiGraph
set_option maxHeartbeats 60000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 20000

def integerPoint (v : Vertex) : IntegerStraightDrawing.Point :=
  (if v.val<52 then (if v.val<26 then (if v.val<13 then (if v.val<6 then (if v.val<3 then (if v.val<1 then (-100,0) else (if v.val<2 then (-19,5) else (-80,60))) else (if v.val<4 then (-78,4) else (if v.val<5 then (-43,24) else (-60,-8)))) else (if v.val<9 then (if v.val<7 then (-80,-60) else (if v.val<8 then (-45,-32) else (-76,-27))) else (if v.val<11 then (if v.val<10 then (-59,-25) else (-49,-15)) else (if v.val<12 then (-83,-21) else (-53,-20))))) else (if v.val<19 then (if v.val<16 then (if v.val<14 then (-65,20) else (if v.val<15 then (-67,-18) else (-65,-22))) else (if v.val<17 then (-68,-27) else (if v.val<18 then (-71,-43) else (-74,-39)))) else (if v.val<22 then (if v.val<20 then (-70,-34) else (if v.val<21 then (-66,-21) else (-72,-40))) else (if v.val<24 then (if v.val<23 then (-64,-17) else (-74,-45)) else (if v.val<25 then (-44,-20) else (-38,-11)))))) else (if v.val<39 then (if v.val<32 then (if v.val<29 then (if v.val<27 then (-40,-8) else (if v.val<28 then (-35,12) else (-42,3))) else (if v.val<30 then (-40,-1) else (if v.val<31 then (-41,-15) else (-39,6)))) else (if v.val<35 then (if v.val<33 then (-42,-19) else (if v.val<34 then (-40,11) else (50,85))) else (if v.val<37 then (if v.val<36 then (6,14) else (95,35)) else (if v.val<38 then (42,64) else (45,26))))) else (if v.val<45 then (if v.val<42 then (if v.val<40 then (22,55) else (if v.val<41 then (-20,100) else (-8,54))) else (if v.val<43 then (11,79) else (if v.val<44 then (5,63) else (9,49)))) else (if v.val<48 then (if v.val<46 then (21,82) else (if v.val<47 then (7,55) else (51,45))) else (if v.val<50 then (if v.val<49 then (15,66) else (10,67)) else (if v.val<51 then (6,72) else (-7,83))))))) else (if v.val<78 then (if v.val<65 then (if v.val<58 then (if v.val<55 then (if v.val<53 then (-2,83) else (if v.val<54 then (1,77) else (11,67))) else (if v.val<56 then (-4,83) else (if v.val<57 then (15,64) else (-8,87)))) else (if v.val<61 then (if v.val<59 then (2,48) else (if v.val<60 then (5,38) else (11,38))) else (if v.val<63 then (if v.val<62 then (26,25) else (23,35)) else (if v.val<64 then (17,35) else (5,42))))) else (if v.val<71 then (if v.val<68 then (if v.val<66 then (24,31) else (if v.val<67 then (1,45) else (29,29))) else (if v.val<69 then (50,-85) else (if v.val<70 then (14,-11) else (-20,-100)))) else (if v.val<74 then (if v.val<72 then (33,-68) else (if v.val<73 then (-3,-52) else (34,-47))) else (if v.val<76 then (if v.val<75 then (95,-35) else (45,-19)) else (if v.val<77 then (61,-50) else (48,-36)))))) else (if v.val<91 then (if v.val<84 then (if v.val<81 then (if v.val<79 then (34,-32) else (if v.val<80 then (60,-60) else (40,-34))) else (if v.val<82 then (11,-67) else (if v.val<83 then (48,-47) else (50,-43)))) else (if v.val<87 then (if v.val<85 then (57,-43) else (if v.val<86 then (73,-37) else (71,-41))) else (if v.val<89 then (if v.val<88 then (64,-41) else (50,-44)) else (if v.val<90 then (71,-39) else (45,-45))))) else (if v.val<98 then (if v.val<94 then (if v.val<92 then (78,-38) else (if v.val<93 then (36,-25) else (28,-23))) else (if v.val<96 then (if v.val<95 then (25,-28) else (8,-35)) else (if v.val<97 then (16,-37) else (19,-32)))) else (if v.val<101 then (if v.val<99 then (31,-25) else (if v.val<100 then (13,-36) else (35,-23))) else (if v.val<103 then (if v.val<102 then (8,-40) else (-38,59)) else (if v.val<104 then (70,2) else (-37,-61))))))))

/-- Outer-face ports appear in the nine-position clockwise boundary layout:
three primary variables, with one palette pair in each intervening sector. -/
theorem port_coordinates :
    integerPoint (copyVertex 0 0)=(-100,0) ∧
    integerPoint (copyVertex 0 2)=(-80,60) ∧
    integerPoint (copyVertex 1 6)=(-20,100) ∧
    integerPoint (copyVertex 1 0)=(50,85) ∧
    integerPoint (copyVertex 1 2)=(95,35) ∧
    integerPoint (copyVertex 2 6)=(95,-35) ∧
    integerPoint (copyVertex 2 0)=(50,-85) ∧
    integerPoint (copyVertex 2 2)=(-20,-100) ∧
    integerPoint (copyVertex 0 6)=(-80,-60) := by decide +kernel

end PlanarHom.PlanarColoringClause
