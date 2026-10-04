import PlanarHom.ColoringMacroFanFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_rotation_b0 : ∀ i : Fin 48, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) := by decide +kernel

private theorem row_rotation_b1 : ∀ i : Fin 48, ((numericRow (host ⟨(48+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(48+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (48+i.val) := by decide +kernel

private theorem row_rotation_b2 : ∀ i : Fin 48, ((numericRow (host ⟨(96+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(96+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (96+i.val) := by decide +kernel

private theorem row_rotation_b3 : ∀ i : Fin 48, ((numericRow (host ⟨(144+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(144+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (144+i.val) := by decide +kernel

private theorem row_rotation_b4 : ∀ i : Fin 48, ((numericRow (host ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) := by decide +kernel

private theorem row_rotation_b5 : ∀ i : Fin 48, ((numericRow (host ⟨(240+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(240+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (240+i.val) := by decide +kernel

private theorem row_rotation_b6 : ∀ i : Fin 48, ((numericRow (host ⟨(288+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(288+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (288+i.val) := by decide +kernel

private theorem row_rotation_b7 : ∀ i : Fin 48, ((numericRow (host ⟨(336+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(336+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (336+i.val) := by decide +kernel

private theorem row_rotation_b8 : ∀ i : Fin 48, ((numericRow (host ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) := by decide +kernel

private theorem row_rotation_b9 : ∀ i : Fin 48, ((numericRow (host ⟨(432+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(432+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (432+i.val) := by decide +kernel

private theorem row_rotation_b10 : ∀ i : Fin 48, ((numericRow (host ⟨(480+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(480+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (480+i.val) := by decide +kernel

private theorem row_rotation_b11 : ∀ i : Fin 48, ((numericRow (host ⟨(528+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(528+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (528+i.val) := by decide +kernel

private theorem row_rotation_b12 : ∀ i : Fin 48, ((numericRow (host ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (576+i.val) := by decide +kernel

private theorem row_rotation_b13 : ∀ i : Fin 48, ((numericRow (host ⟨(624+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(624+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (624+i.val) := by decide +kernel

private theorem row_rotation_b14 : ∀ i : Fin 48, ((numericRow (host ⟨(672+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(672+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (672+i.val) := by decide +kernel

private theorem row_rotation_b15 : ∀ i : Fin 48, ((numericRow (host ⟨(720+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(720+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (720+i.val) := by decide +kernel

private theorem row_rotation_b16 : ∀ i : Fin 48, ((numericRow (host ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (768+i.val) := by decide +kernel

private theorem row_rotation_b17 : ∀ i : Fin 48, ((numericRow (host ⟨(816+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(816+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (816+i.val) := by decide +kernel

private theorem row_rotation_b18 : ∀ i : Fin 48, ((numericRow (host ⟨(864+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(864+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (864+i.val) := by decide +kernel

private theorem row_rotation_b19 : ∀ i : Fin 48, ((numericRow (host ⟨(912+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(912+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (912+i.val) := by decide +kernel

private theorem row_rotation_b20 : ∀ i : Fin 48, ((numericRow (host ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (960+i.val) := by decide +kernel

private theorem row_rotation_b21 : ∀ i : Fin 48, ((numericRow (host ⟨(1008+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1008+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1008+i.val) := by decide +kernel

private theorem row_rotation_b22 : ∀ i : Fin 48, ((numericRow (host ⟨(1056+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1056+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1056+i.val) := by decide +kernel

private theorem row_rotation_b23 : ∀ i : Fin 48, ((numericRow (host ⟨(1104+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1104+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1104+i.val) := by decide +kernel

private theorem row_rotation_b24 : ∀ i : Fin 48, ((numericRow (host ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1152+i.val) := by decide +kernel

private theorem row_rotation_b25 : ∀ i : Fin 48, ((numericRow (host ⟨(1200+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1200+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1200+i.val) := by decide +kernel

private theorem row_rotation_b26 : ∀ i : Fin 48, ((numericRow (host ⟨(1248+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1248+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1248+i.val) := by decide +kernel

private theorem row_rotation_b27 : ∀ i : Fin 48, ((numericRow (host ⟨(1296+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1296+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1296+i.val) := by decide +kernel

private theorem row_rotation_b28 : ∀ i : Fin 48, ((numericRow (host ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1344+i.val) := by decide +kernel

private theorem row_rotation_b29 : ∀ i : Fin 48, ((numericRow (host ⟨(1392+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1392+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1392+i.val) := by decide +kernel

private theorem row_rotation_b30 : ∀ i : Fin 48, ((numericRow (host ⟨(1440+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1440+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1440+i.val) := by decide +kernel

private theorem row_rotation_b31 : ∀ i : Fin 48, ((numericRow (host ⟨(1488+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1488+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1488+i.val) := by decide +kernel

private theorem row_rotation_b32 : ∀ i : Fin 48, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) := by decide +kernel

private theorem row_rotation_b33 : ∀ i : Fin 48, ((numericRow (host ⟨(1584+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1584+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1584+i.val) := by decide +kernel

private theorem row_rotation_b34 : ∀ i : Fin 48, ((numericRow (host ⟨(1632+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1632+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1632+i.val) := by decide +kernel

private theorem row_rotation_b35 : ∀ i : Fin 48, ((numericRow (host ⟨(1680+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1680+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1680+i.val) := by decide +kernel

private theorem row_rotation_b36 : ∀ i : Fin 48, ((numericRow (host ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1728+i.val) := by decide +kernel

private theorem row_rotation_b37 : ∀ i : Fin 48, ((numericRow (host ⟨(1776+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1776+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1776+i.val) := by decide +kernel

private theorem row_rotation_b38 : ∀ i : Fin 48, ((numericRow (host ⟨(1824+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1824+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1824+i.val) := by decide +kernel

private theorem row_rotation_b39 : ∀ i : Fin 48, ((numericRow (host ⟨(1872+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1872+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1872+i.val) := by decide +kernel

private theorem row_rotation_b40 : ∀ i : Fin 48, ((numericRow (host ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1920+i.val) := by decide +kernel

private theorem row_rotation_b41 : ∀ i : Fin 48, ((numericRow (host ⟨(1968+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1968+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1968+i.val) := by decide +kernel

private theorem row_rotation_b42 : ∀ i : Fin 48, ((numericRow (host ⟨(2016+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2016+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2016+i.val) := by decide +kernel

private theorem row_rotation_b43 : ∀ i : Fin 48, ((numericRow (host ⟨(2064+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2064+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2064+i.val) := by decide +kernel

private theorem row_rotation_b44 : ∀ i : Fin 48, ((numericRow (host ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2112+i.val) := by decide +kernel

private theorem row_rotation_b45 : ∀ i : Fin 48, ((numericRow (host ⟨(2160+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2160+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2160+i.val) := by decide +kernel

private theorem row_rotation_b46 : ∀ i : Fin 48, ((numericRow (host ⟨(2208+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2208+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2208+i.val) := by decide +kernel

private theorem row_rotation_b47 : ∀ i : Fin 48, ((numericRow (host ⟨(2256+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2256+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2256+i.val) := by decide +kernel

private theorem row_rotation_b48 : ∀ i : Fin 48, ((numericRow (host ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2304+i.val) := by decide +kernel

private theorem row_rotation_b49 : ∀ i : Fin 48, ((numericRow (host ⟨(2352+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2352+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2352+i.val) := by decide +kernel

private theorem row_rotation_b50 : ∀ i : Fin 48, ((numericRow (host ⟨(2400+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2400+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2400+i.val) := by decide +kernel

private theorem row_rotation_b51 : ∀ i : Fin 48, ((numericRow (host ⟨(2448+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2448+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2448+i.val) := by decide +kernel

private theorem row_rotation_b52 : ∀ i : Fin 48, ((numericRow (host ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2496+i.val) := by decide +kernel

private theorem row_rotation_b53 : ∀ i : Fin 48, ((numericRow (host ⟨(2544+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2544+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2544+i.val) := by decide +kernel

private theorem row_rotation_b54 : ∀ i : Fin 48, ((numericRow (host ⟨(2592+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2592+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2592+i.val) := by decide +kernel

private theorem row_rotation_b55 : ∀ i : Fin 48, ((numericRow (host ⟨(2640+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2640+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2640+i.val) := by decide +kernel

private theorem row_rotation_b56 : ∀ i : Fin 48, ((numericRow (host ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2688+i.val) := by decide +kernel

private theorem row_rotation_b57 : ∀ i : Fin 48, ((numericRow (host ⟨(2736+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2736+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2736+i.val) := by decide +kernel

private theorem row_rotation_b58 : ∀ i : Fin 48, ((numericRow (host ⟨(2784+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2784+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2784+i.val) := by decide +kernel

private theorem row_rotation_b59 : ∀ i : Fin 48, ((numericRow (host ⟨(2832+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2832+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2832+i.val) := by decide +kernel

private theorem row_rotation_b60 : ∀ i : Fin 48, ((numericRow (host ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2880+i.val) := by decide +kernel

private theorem row_rotation_b61 : ∀ i : Fin 48, ((numericRow (host ⟨(2928+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2928+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2928+i.val) := by decide +kernel

private theorem row_rotation_b62 : ∀ i : Fin 48, ((numericRow (host ⟨(2976+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2976+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2976+i.val) := by decide +kernel

private theorem row_rotation_b63 : ∀ i : Fin 48, ((numericRow (host ⟨(3024+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3024+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3024+i.val) := by decide +kernel

private theorem row_rotation_b64 : ∀ i : Fin 48, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) := by decide +kernel

private theorem row_rotation_b65 : ∀ i : Fin 48, ((numericRow (host ⟨(3120+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3120+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3120+i.val) := by decide +kernel

private theorem row_rotation_b66 : ∀ i : Fin 48, ((numericRow (host ⟨(3168+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3168+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3168+i.val) := by decide +kernel

private theorem row_rotation_b67 : ∀ i : Fin 48, ((numericRow (host ⟨(3216+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3216+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3216+i.val) := by decide +kernel

private theorem row_rotation_b68 : ∀ i : Fin 48, ((numericRow (host ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3264+i.val) := by decide +kernel

private theorem row_rotation_b69 : ∀ i : Fin 48, ((numericRow (host ⟨(3312+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3312+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3312+i.val) := by decide +kernel

private theorem row_rotation_b70 : ∀ i : Fin 48, ((numericRow (host ⟨(3360+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3360+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3360+i.val) := by decide +kernel

private theorem row_rotation_b71 : ∀ i : Fin 48, ((numericRow (host ⟨(3408+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3408+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3408+i.val) := by decide +kernel

private theorem row_rotation_b72 : ∀ i : Fin 48, ((numericRow (host ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3456+i.val) := by decide +kernel

private theorem row_rotation_b73 : ∀ i : Fin 48, ((numericRow (host ⟨(3504+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3504+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3504+i.val) := by decide +kernel

private theorem row_rotation_b74 : ∀ i : Fin 48, ((numericRow (host ⟨(3552+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3552+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3552+i.val) := by decide +kernel

private theorem row_rotation_b75 : ∀ i : Fin 48, ((numericRow (host ⟨(3600+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3600+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3600+i.val) := by decide +kernel

private theorem row_rotation_b76 : ∀ i : Fin 48, ((numericRow (host ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3648+i.val) := by decide +kernel

private theorem row_rotation_b77 : ∀ i : Fin 48, ((numericRow (host ⟨(3696+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3696+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3696+i.val) := by decide +kernel

private theorem row_rotation_b78 : ∀ i : Fin 48, ((numericRow (host ⟨(3744+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3744+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3744+i.val) := by decide +kernel

private theorem row_rotation_b79 : ∀ i : Fin 48, ((numericRow (host ⟨(3792+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3792+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3792+i.val) := by decide +kernel

private theorem row_rotation_b80 : ∀ i : Fin 48, ((numericRow (host ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3840+i.val) := by decide +kernel

private theorem row_rotation_b81 : ∀ i : Fin 48, ((numericRow (host ⟨(3888+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3888+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3888+i.val) := by decide +kernel

private theorem row_rotation_b82 : ∀ i : Fin 48, ((numericRow (host ⟨(3936+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3936+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3936+i.val) := by decide +kernel

private theorem row_rotation_b83 : ∀ i : Fin 48, ((numericRow (host ⟨(3984+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3984+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3984+i.val) := by decide +kernel

private theorem row_rotation_b84 : ∀ i : Fin 48, ((numericRow (host ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4032+i.val) := by decide +kernel

private theorem row_rotation_b85 : ∀ i : Fin 48, ((numericRow (host ⟨(4080+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4080+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4080+i.val) := by decide +kernel

private theorem row_rotation_b86 : ∀ i : Fin 48, ((numericRow (host ⟨(4128+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4128+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4128+i.val) := by decide +kernel

private theorem row_rotation_b87 : ∀ i : Fin 48, ((numericRow (host ⟨(4176+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4176+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4176+i.val) := by decide +kernel

private theorem row_rotation_b88 : ∀ i : Fin 48, ((numericRow (host ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4224+i.val) := by decide +kernel

private theorem row_rotation_b89 : ∀ i : Fin 48, ((numericRow (host ⟨(4272+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4272+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4272+i.val) := by decide +kernel

private theorem row_rotation_b90 : ∀ i : Fin 48, ((numericRow (host ⟨(4320+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4320+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4320+i.val) := by decide +kernel

private theorem row_rotation_b91 : ∀ i : Fin 48, ((numericRow (host ⟨(4368+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4368+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4368+i.val) := by decide +kernel

private theorem row_rotation_b92 : ∀ i : Fin 48, ((numericRow (host ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4416+i.val) := by decide +kernel

private theorem row_rotation_b93 : ∀ i : Fin 48, ((numericRow (host ⟨(4464+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4464+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4464+i.val) := by decide +kernel

private theorem row_rotation_b94 : ∀ i : Fin 48, ((numericRow (host ⟨(4512+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4512+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4512+i.val) := by decide +kernel

private theorem row_rotation_b95 : ∀ i : Fin 48, ((numericRow (host ⟨(4560+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4560+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4560+i.val) := by decide +kernel

private theorem row_rotation_b96 : ∀ i : Fin 48, ((numericRow (host ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4608+i.val) := by decide +kernel

private theorem row_rotation_b97 : ∀ i : Fin 48, ((numericRow (host ⟨(4656+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4656+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4656+i.val) := by decide +kernel

private theorem row_rotation_b98 : ∀ i : Fin 48, ((numericRow (host ⟨(4704+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4704+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4704+i.val) := by decide +kernel

private theorem row_rotation_b99 : ∀ i : Fin 48, ((numericRow (host ⟨(4752+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4752+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4752+i.val) := by decide +kernel

private theorem row_rotation_b100 : ∀ i : Fin 48, ((numericRow (host ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4800+i.val) := by decide +kernel

private theorem row_rotation_b101 : ∀ i : Fin 48, ((numericRow (host ⟨(4848+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4848+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4848+i.val) := by decide +kernel

private theorem row_rotation_b102 : ∀ i : Fin 48, ((numericRow (host ⟨(4896+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4896+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4896+i.val) := by decide +kernel

private theorem row_rotation_b103 : ∀ i : Fin 48, ((numericRow (host ⟨(4944+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4944+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4944+i.val) := by decide +kernel

private theorem row_rotation_b104 : ∀ i : Fin 48, ((numericRow (host ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4992+i.val) := by decide +kernel

private theorem row_rotation_b105 : ∀ i : Fin 48, ((numericRow (host ⟨(5040+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5040+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5040+i.val) := by decide +kernel

private theorem row_rotation_b106 : ∀ i : Fin 48, ((numericRow (host ⟨(5088+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5088+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5088+i.val) := by decide +kernel

private theorem row_rotation_b107 : ∀ i : Fin 48, ((numericRow (host ⟨(5136+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5136+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5136+i.val) := by decide +kernel

private theorem row_rotation_b108 : ∀ i : Fin 48, ((numericRow (host ⟨(5184+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5184+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5184+i.val) := by decide +kernel

private theorem row_rotation_b109 : ∀ i : Fin 32, ((numericRow (host ⟨(5232+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5232+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5232+i.val) := by decide +kernel

private theorem row_rotation_n0_0 : ∀ i : Fin 96, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 48 48 row_rotation_b0 row_rotation_b1

private theorem row_rotation_n0_1 : ∀ i : Fin 96, ((numericRow (host ⟨(96+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(96+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 96 48 48 row_rotation_b2 row_rotation_b3

private theorem row_rotation_n0_2 : ∀ i : Fin 96, ((numericRow (host ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 192 48 48 row_rotation_b4 row_rotation_b5

private theorem row_rotation_n0_3 : ∀ i : Fin 96, ((numericRow (host ⟨(288+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(288+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 288 48 48 row_rotation_b6 row_rotation_b7

private theorem row_rotation_n0_4 : ∀ i : Fin 96, ((numericRow (host ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 384 48 48 row_rotation_b8 row_rotation_b9

private theorem row_rotation_n0_5 : ∀ i : Fin 96, ((numericRow (host ⟨(480+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(480+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 480 48 48 row_rotation_b10 row_rotation_b11

private theorem row_rotation_n0_6 : ∀ i : Fin 96, ((numericRow (host ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 576 48 48 row_rotation_b12 row_rotation_b13

private theorem row_rotation_n0_7 : ∀ i : Fin 96, ((numericRow (host ⟨(672+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(672+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (672+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 672 48 48 row_rotation_b14 row_rotation_b15

private theorem row_rotation_n0_8 : ∀ i : Fin 96, ((numericRow (host ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 768 48 48 row_rotation_b16 row_rotation_b17

private theorem row_rotation_n0_9 : ∀ i : Fin 96, ((numericRow (host ⟨(864+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(864+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (864+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 864 48 48 row_rotation_b18 row_rotation_b19

private theorem row_rotation_n0_10 : ∀ i : Fin 96, ((numericRow (host ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 960 48 48 row_rotation_b20 row_rotation_b21

private theorem row_rotation_n0_11 : ∀ i : Fin 96, ((numericRow (host ⟨(1056+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1056+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1056+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1056 48 48 row_rotation_b22 row_rotation_b23

private theorem row_rotation_n0_12 : ∀ i : Fin 96, ((numericRow (host ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1152 48 48 row_rotation_b24 row_rotation_b25

private theorem row_rotation_n0_13 : ∀ i : Fin 96, ((numericRow (host ⟨(1248+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1248+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1248+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1248 48 48 row_rotation_b26 row_rotation_b27

private theorem row_rotation_n0_14 : ∀ i : Fin 96, ((numericRow (host ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1344 48 48 row_rotation_b28 row_rotation_b29

private theorem row_rotation_n0_15 : ∀ i : Fin 96, ((numericRow (host ⟨(1440+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1440+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1440+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1440 48 48 row_rotation_b30 row_rotation_b31

private theorem row_rotation_n0_16 : ∀ i : Fin 96, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1536 48 48 row_rotation_b32 row_rotation_b33

private theorem row_rotation_n0_17 : ∀ i : Fin 96, ((numericRow (host ⟨(1632+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1632+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1632+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1632 48 48 row_rotation_b34 row_rotation_b35

private theorem row_rotation_n0_18 : ∀ i : Fin 96, ((numericRow (host ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1728 48 48 row_rotation_b36 row_rotation_b37

private theorem row_rotation_n0_19 : ∀ i : Fin 96, ((numericRow (host ⟨(1824+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1824+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1824+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1824 48 48 row_rotation_b38 row_rotation_b39

private theorem row_rotation_n0_20 : ∀ i : Fin 96, ((numericRow (host ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1920 48 48 row_rotation_b40 row_rotation_b41

private theorem row_rotation_n0_21 : ∀ i : Fin 96, ((numericRow (host ⟨(2016+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2016+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2016+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2016 48 48 row_rotation_b42 row_rotation_b43

private theorem row_rotation_n0_22 : ∀ i : Fin 96, ((numericRow (host ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2112 48 48 row_rotation_b44 row_rotation_b45

private theorem row_rotation_n0_23 : ∀ i : Fin 96, ((numericRow (host ⟨(2208+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2208+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2208+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2208 48 48 row_rotation_b46 row_rotation_b47

private theorem row_rotation_n0_24 : ∀ i : Fin 96, ((numericRow (host ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2304 48 48 row_rotation_b48 row_rotation_b49

private theorem row_rotation_n0_25 : ∀ i : Fin 96, ((numericRow (host ⟨(2400+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2400+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2400+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2400 48 48 row_rotation_b50 row_rotation_b51

private theorem row_rotation_n0_26 : ∀ i : Fin 96, ((numericRow (host ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2496 48 48 row_rotation_b52 row_rotation_b53

private theorem row_rotation_n0_27 : ∀ i : Fin 96, ((numericRow (host ⟨(2592+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2592+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2592+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2592 48 48 row_rotation_b54 row_rotation_b55

private theorem row_rotation_n0_28 : ∀ i : Fin 96, ((numericRow (host ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2688 48 48 row_rotation_b56 row_rotation_b57

private theorem row_rotation_n0_29 : ∀ i : Fin 96, ((numericRow (host ⟨(2784+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2784+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2784+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2784 48 48 row_rotation_b58 row_rotation_b59

private theorem row_rotation_n0_30 : ∀ i : Fin 96, ((numericRow (host ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2880 48 48 row_rotation_b60 row_rotation_b61

private theorem row_rotation_n0_31 : ∀ i : Fin 96, ((numericRow (host ⟨(2976+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2976+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2976+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2976 48 48 row_rotation_b62 row_rotation_b63

private theorem row_rotation_n0_32 : ∀ i : Fin 96, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 48 48 row_rotation_b64 row_rotation_b65

private theorem row_rotation_n0_33 : ∀ i : Fin 96, ((numericRow (host ⟨(3168+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3168+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3168+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3168 48 48 row_rotation_b66 row_rotation_b67

private theorem row_rotation_n0_34 : ∀ i : Fin 96, ((numericRow (host ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3264 48 48 row_rotation_b68 row_rotation_b69

private theorem row_rotation_n0_35 : ∀ i : Fin 96, ((numericRow (host ⟨(3360+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3360+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3360+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3360 48 48 row_rotation_b70 row_rotation_b71

private theorem row_rotation_n0_36 : ∀ i : Fin 96, ((numericRow (host ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3456 48 48 row_rotation_b72 row_rotation_b73

private theorem row_rotation_n0_37 : ∀ i : Fin 96, ((numericRow (host ⟨(3552+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3552+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3552+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3552 48 48 row_rotation_b74 row_rotation_b75

private theorem row_rotation_n0_38 : ∀ i : Fin 96, ((numericRow (host ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3648 48 48 row_rotation_b76 row_rotation_b77

private theorem row_rotation_n0_39 : ∀ i : Fin 96, ((numericRow (host ⟨(3744+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3744+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3744+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3744 48 48 row_rotation_b78 row_rotation_b79

private theorem row_rotation_n0_40 : ∀ i : Fin 96, ((numericRow (host ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3840 48 48 row_rotation_b80 row_rotation_b81

private theorem row_rotation_n0_41 : ∀ i : Fin 96, ((numericRow (host ⟨(3936+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3936+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3936+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3936 48 48 row_rotation_b82 row_rotation_b83

private theorem row_rotation_n0_42 : ∀ i : Fin 96, ((numericRow (host ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4032 48 48 row_rotation_b84 row_rotation_b85

private theorem row_rotation_n0_43 : ∀ i : Fin 96, ((numericRow (host ⟨(4128+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4128+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4128+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4128 48 48 row_rotation_b86 row_rotation_b87

private theorem row_rotation_n0_44 : ∀ i : Fin 96, ((numericRow (host ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4224 48 48 row_rotation_b88 row_rotation_b89

private theorem row_rotation_n0_45 : ∀ i : Fin 96, ((numericRow (host ⟨(4320+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4320+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4320+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4320 48 48 row_rotation_b90 row_rotation_b91

private theorem row_rotation_n0_46 : ∀ i : Fin 96, ((numericRow (host ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4416 48 48 row_rotation_b92 row_rotation_b93

private theorem row_rotation_n0_47 : ∀ i : Fin 96, ((numericRow (host ⟨(4512+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4512+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4512+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4512 48 48 row_rotation_b94 row_rotation_b95

private theorem row_rotation_n0_48 : ∀ i : Fin 96, ((numericRow (host ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4608 48 48 row_rotation_b96 row_rotation_b97

private theorem row_rotation_n0_49 : ∀ i : Fin 96, ((numericRow (host ⟨(4704+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4704+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4704+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4704 48 48 row_rotation_b98 row_rotation_b99

private theorem row_rotation_n0_50 : ∀ i : Fin 96, ((numericRow (host ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4800 48 48 row_rotation_b100 row_rotation_b101

private theorem row_rotation_n0_51 : ∀ i : Fin 96, ((numericRow (host ⟨(4896+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4896+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4896+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4896 48 48 row_rotation_b102 row_rotation_b103

private theorem row_rotation_n0_52 : ∀ i : Fin 96, ((numericRow (host ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4992 48 48 row_rotation_b104 row_rotation_b105

private theorem row_rotation_n0_53 : ∀ i : Fin 96, ((numericRow (host ⟨(5088+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5088+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5088+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 5088 48 48 row_rotation_b106 row_rotation_b107

private theorem row_rotation_n0_54 : ∀ i : Fin 80, ((numericRow (host ⟨(5184+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(5184+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (5184+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 5184 48 32 row_rotation_b108 row_rotation_b109

private theorem row_rotation_n1_0 : ∀ i : Fin 192, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 96 96 row_rotation_n0_0 row_rotation_n0_1

private theorem row_rotation_n1_1 : ∀ i : Fin 192, ((numericRow (host ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 192 96 96 row_rotation_n0_2 row_rotation_n0_3

private theorem row_rotation_n1_2 : ∀ i : Fin 192, ((numericRow (host ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 384 96 96 row_rotation_n0_4 row_rotation_n0_5

private theorem row_rotation_n1_3 : ∀ i : Fin 192, ((numericRow (host ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(576+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 576 96 96 row_rotation_n0_6 row_rotation_n0_7

private theorem row_rotation_n1_4 : ∀ i : Fin 192, ((numericRow (host ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 768 96 96 row_rotation_n0_8 row_rotation_n0_9

private theorem row_rotation_n1_5 : ∀ i : Fin 192, ((numericRow (host ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(960+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 960 96 96 row_rotation_n0_10 row_rotation_n0_11

private theorem row_rotation_n1_6 : ∀ i : Fin 192, ((numericRow (host ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1152 96 96 row_rotation_n0_12 row_rotation_n0_13

private theorem row_rotation_n1_7 : ∀ i : Fin 192, ((numericRow (host ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1344+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1344 96 96 row_rotation_n0_14 row_rotation_n0_15

private theorem row_rotation_n1_8 : ∀ i : Fin 192, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1536 96 96 row_rotation_n0_16 row_rotation_n0_17

private theorem row_rotation_n1_9 : ∀ i : Fin 192, ((numericRow (host ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1728+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1728 96 96 row_rotation_n0_18 row_rotation_n0_19

private theorem row_rotation_n1_10 : ∀ i : Fin 192, ((numericRow (host ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1920 96 96 row_rotation_n0_20 row_rotation_n0_21

private theorem row_rotation_n1_11 : ∀ i : Fin 192, ((numericRow (host ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2112+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2112 96 96 row_rotation_n0_22 row_rotation_n0_23

private theorem row_rotation_n1_12 : ∀ i : Fin 192, ((numericRow (host ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2304 96 96 row_rotation_n0_24 row_rotation_n0_25

private theorem row_rotation_n1_13 : ∀ i : Fin 192, ((numericRow (host ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2496+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2496 96 96 row_rotation_n0_26 row_rotation_n0_27

private theorem row_rotation_n1_14 : ∀ i : Fin 192, ((numericRow (host ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2688 96 96 row_rotation_n0_28 row_rotation_n0_29

private theorem row_rotation_n1_15 : ∀ i : Fin 192, ((numericRow (host ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2880+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2880 96 96 row_rotation_n0_30 row_rotation_n0_31

private theorem row_rotation_n1_16 : ∀ i : Fin 192, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 96 96 row_rotation_n0_32 row_rotation_n0_33

private theorem row_rotation_n1_17 : ∀ i : Fin 192, ((numericRow (host ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3264+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3264 96 96 row_rotation_n0_34 row_rotation_n0_35

private theorem row_rotation_n1_18 : ∀ i : Fin 192, ((numericRow (host ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3456 96 96 row_rotation_n0_36 row_rotation_n0_37

private theorem row_rotation_n1_19 : ∀ i : Fin 192, ((numericRow (host ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3648+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3648 96 96 row_rotation_n0_38 row_rotation_n0_39

private theorem row_rotation_n1_20 : ∀ i : Fin 192, ((numericRow (host ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3840 96 96 row_rotation_n0_40 row_rotation_n0_41

private theorem row_rotation_n1_21 : ∀ i : Fin 192, ((numericRow (host ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4032+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4032 96 96 row_rotation_n0_42 row_rotation_n0_43

private theorem row_rotation_n1_22 : ∀ i : Fin 192, ((numericRow (host ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4224 96 96 row_rotation_n0_44 row_rotation_n0_45

private theorem row_rotation_n1_23 : ∀ i : Fin 192, ((numericRow (host ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4416+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4416 96 96 row_rotation_n0_46 row_rotation_n0_47

private theorem row_rotation_n1_24 : ∀ i : Fin 192, ((numericRow (host ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4608 96 96 row_rotation_n0_48 row_rotation_n0_49

private theorem row_rotation_n1_25 : ∀ i : Fin 192, ((numericRow (host ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4800+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4800 96 96 row_rotation_n0_50 row_rotation_n0_51

private theorem row_rotation_n1_26 : ∀ i : Fin 192, ((numericRow (host ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4992 96 96 row_rotation_n0_52 row_rotation_n0_53

private theorem row_rotation_n2_0 : ∀ i : Fin 384, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 192 192 row_rotation_n1_0 row_rotation_n1_1

private theorem row_rotation_n2_1 : ∀ i : Fin 384, ((numericRow (host ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 384 192 192 row_rotation_n1_2 row_rotation_n1_3

private theorem row_rotation_n2_2 : ∀ i : Fin 384, ((numericRow (host ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 768 192 192 row_rotation_n1_4 row_rotation_n1_5

private theorem row_rotation_n2_3 : ∀ i : Fin 384, ((numericRow (host ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1152+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1152 192 192 row_rotation_n1_6 row_rotation_n1_7

private theorem row_rotation_n2_4 : ∀ i : Fin 384, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1536 192 192 row_rotation_n1_8 row_rotation_n1_9

private theorem row_rotation_n2_5 : ∀ i : Fin 384, ((numericRow (host ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1920+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1920 192 192 row_rotation_n1_10 row_rotation_n1_11

private theorem row_rotation_n2_6 : ∀ i : Fin 384, ((numericRow (host ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2304 192 192 row_rotation_n1_12 row_rotation_n1_13

private theorem row_rotation_n2_7 : ∀ i : Fin 384, ((numericRow (host ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2688+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2688 192 192 row_rotation_n1_14 row_rotation_n1_15

private theorem row_rotation_n2_8 : ∀ i : Fin 384, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 192 192 row_rotation_n1_16 row_rotation_n1_17

private theorem row_rotation_n2_9 : ∀ i : Fin 384, ((numericRow (host ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3456+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3456 192 192 row_rotation_n1_18 row_rotation_n1_19

private theorem row_rotation_n2_10 : ∀ i : Fin 384, ((numericRow (host ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3840 192 192 row_rotation_n1_20 row_rotation_n1_21

private theorem row_rotation_n2_11 : ∀ i : Fin 384, ((numericRow (host ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4224+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4224 192 192 row_rotation_n1_22 row_rotation_n1_23

private theorem row_rotation_n2_12 : ∀ i : Fin 384, ((numericRow (host ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4608 192 192 row_rotation_n1_24 row_rotation_n1_25

private theorem row_rotation_n2_13 : ∀ i : Fin 272, ((numericRow (host ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4992+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4992 192 80 row_rotation_n1_26 row_rotation_n0_54

private theorem row_rotation_n3_0 : ∀ i : Fin 768, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 384 384 row_rotation_n2_0 row_rotation_n2_1

private theorem row_rotation_n3_1 : ∀ i : Fin 768, ((numericRow (host ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(768+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 768 384 384 row_rotation_n2_2 row_rotation_n2_3

private theorem row_rotation_n3_2 : ∀ i : Fin 768, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1536 384 384 row_rotation_n2_4 row_rotation_n2_5

private theorem row_rotation_n3_3 : ∀ i : Fin 768, ((numericRow (host ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(2304+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 2304 384 384 row_rotation_n2_6 row_rotation_n2_7

private theorem row_rotation_n3_4 : ∀ i : Fin 768, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 384 384 row_rotation_n2_8 row_rotation_n2_9

private theorem row_rotation_n3_5 : ∀ i : Fin 768, ((numericRow (host ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3840+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3840 384 384 row_rotation_n2_10 row_rotation_n2_11

private theorem row_rotation_n3_6 : ∀ i : Fin 656, ((numericRow (host ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(4608+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 4608 384 272 row_rotation_n2_12 row_rotation_n2_13

private theorem row_rotation_n4_0 : ∀ i : Fin 1536, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 768 768 row_rotation_n3_0 row_rotation_n3_1

private theorem row_rotation_n4_1 : ∀ i : Fin 1536, ((numericRow (host ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(1536+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 1536 768 768 row_rotation_n3_2 row_rotation_n3_3

private theorem row_rotation_n4_2 : ∀ i : Fin 1536, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 768 768 row_rotation_n3_4 row_rotation_n3_5

private theorem row_rotation_n5_0 : ∀ i : Fin 3072, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 1536 1536 row_rotation_n4_0 row_rotation_n4_1

private theorem row_rotation_n5_1 : ∀ i : Fin 2192, ((numericRow (host ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(3072+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 3072 1536 656 row_rotation_n4_2 row_rotation_n3_6

private theorem row_rotation_n6_0 : ∀ i : Fin 5264, ((numericRow (host ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 3072 2192 row_rotation_n5_0 row_rotation_n5_1

theorem row_rotation : ∀ i : Fin 5264, ((numericRow (host ⟨i.val%5264,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i.val%5264,Nat.mod_lt _ (by decide)⟩).val=rotateValue i.val := by
  simpa only [Nat.zero_add] using row_rotation_n6_0

end PlanarHom.ColoringMacroFaces.FanFramed
