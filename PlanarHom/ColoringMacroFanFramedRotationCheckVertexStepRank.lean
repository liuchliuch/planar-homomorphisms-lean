import PlanarHom.ColoringMacroFanFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_step_rank_b0 : ∀ i : Fin 48, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) := by decide +kernel

private theorem vertex_step_rank_b1 : ∀ i : Fin 48, 0 < vertexRankValue (48+i.val) → vertexRankValue (rotateValue (48+i.val)) + 1 = vertexRankValue (48+i.val) := by decide +kernel

private theorem vertex_step_rank_b2 : ∀ i : Fin 48, 0 < vertexRankValue (96+i.val) → vertexRankValue (rotateValue (96+i.val)) + 1 = vertexRankValue (96+i.val) := by decide +kernel

private theorem vertex_step_rank_b3 : ∀ i : Fin 48, 0 < vertexRankValue (144+i.val) → vertexRankValue (rotateValue (144+i.val)) + 1 = vertexRankValue (144+i.val) := by decide +kernel

private theorem vertex_step_rank_b4 : ∀ i : Fin 48, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) := by decide +kernel

private theorem vertex_step_rank_b5 : ∀ i : Fin 48, 0 < vertexRankValue (240+i.val) → vertexRankValue (rotateValue (240+i.val)) + 1 = vertexRankValue (240+i.val) := by decide +kernel

private theorem vertex_step_rank_b6 : ∀ i : Fin 48, 0 < vertexRankValue (288+i.val) → vertexRankValue (rotateValue (288+i.val)) + 1 = vertexRankValue (288+i.val) := by decide +kernel

private theorem vertex_step_rank_b7 : ∀ i : Fin 48, 0 < vertexRankValue (336+i.val) → vertexRankValue (rotateValue (336+i.val)) + 1 = vertexRankValue (336+i.val) := by decide +kernel

private theorem vertex_step_rank_b8 : ∀ i : Fin 48, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) := by decide +kernel

private theorem vertex_step_rank_b9 : ∀ i : Fin 48, 0 < vertexRankValue (432+i.val) → vertexRankValue (rotateValue (432+i.val)) + 1 = vertexRankValue (432+i.val) := by decide +kernel

private theorem vertex_step_rank_b10 : ∀ i : Fin 48, 0 < vertexRankValue (480+i.val) → vertexRankValue (rotateValue (480+i.val)) + 1 = vertexRankValue (480+i.val) := by decide +kernel

private theorem vertex_step_rank_b11 : ∀ i : Fin 48, 0 < vertexRankValue (528+i.val) → vertexRankValue (rotateValue (528+i.val)) + 1 = vertexRankValue (528+i.val) := by decide +kernel

private theorem vertex_step_rank_b12 : ∀ i : Fin 48, 0 < vertexRankValue (576+i.val) → vertexRankValue (rotateValue (576+i.val)) + 1 = vertexRankValue (576+i.val) := by decide +kernel

private theorem vertex_step_rank_b13 : ∀ i : Fin 48, 0 < vertexRankValue (624+i.val) → vertexRankValue (rotateValue (624+i.val)) + 1 = vertexRankValue (624+i.val) := by decide +kernel

private theorem vertex_step_rank_b14 : ∀ i : Fin 48, 0 < vertexRankValue (672+i.val) → vertexRankValue (rotateValue (672+i.val)) + 1 = vertexRankValue (672+i.val) := by decide +kernel

private theorem vertex_step_rank_b15 : ∀ i : Fin 48, 0 < vertexRankValue (720+i.val) → vertexRankValue (rotateValue (720+i.val)) + 1 = vertexRankValue (720+i.val) := by decide +kernel

private theorem vertex_step_rank_b16 : ∀ i : Fin 48, 0 < vertexRankValue (768+i.val) → vertexRankValue (rotateValue (768+i.val)) + 1 = vertexRankValue (768+i.val) := by decide +kernel

private theorem vertex_step_rank_b17 : ∀ i : Fin 48, 0 < vertexRankValue (816+i.val) → vertexRankValue (rotateValue (816+i.val)) + 1 = vertexRankValue (816+i.val) := by decide +kernel

private theorem vertex_step_rank_b18 : ∀ i : Fin 48, 0 < vertexRankValue (864+i.val) → vertexRankValue (rotateValue (864+i.val)) + 1 = vertexRankValue (864+i.val) := by decide +kernel

private theorem vertex_step_rank_b19 : ∀ i : Fin 48, 0 < vertexRankValue (912+i.val) → vertexRankValue (rotateValue (912+i.val)) + 1 = vertexRankValue (912+i.val) := by decide +kernel

private theorem vertex_step_rank_b20 : ∀ i : Fin 48, 0 < vertexRankValue (960+i.val) → vertexRankValue (rotateValue (960+i.val)) + 1 = vertexRankValue (960+i.val) := by decide +kernel

private theorem vertex_step_rank_b21 : ∀ i : Fin 48, 0 < vertexRankValue (1008+i.val) → vertexRankValue (rotateValue (1008+i.val)) + 1 = vertexRankValue (1008+i.val) := by decide +kernel

private theorem vertex_step_rank_b22 : ∀ i : Fin 48, 0 < vertexRankValue (1056+i.val) → vertexRankValue (rotateValue (1056+i.val)) + 1 = vertexRankValue (1056+i.val) := by decide +kernel

private theorem vertex_step_rank_b23 : ∀ i : Fin 48, 0 < vertexRankValue (1104+i.val) → vertexRankValue (rotateValue (1104+i.val)) + 1 = vertexRankValue (1104+i.val) := by decide +kernel

private theorem vertex_step_rank_b24 : ∀ i : Fin 48, 0 < vertexRankValue (1152+i.val) → vertexRankValue (rotateValue (1152+i.val)) + 1 = vertexRankValue (1152+i.val) := by decide +kernel

private theorem vertex_step_rank_b25 : ∀ i : Fin 48, 0 < vertexRankValue (1200+i.val) → vertexRankValue (rotateValue (1200+i.val)) + 1 = vertexRankValue (1200+i.val) := by decide +kernel

private theorem vertex_step_rank_b26 : ∀ i : Fin 48, 0 < vertexRankValue (1248+i.val) → vertexRankValue (rotateValue (1248+i.val)) + 1 = vertexRankValue (1248+i.val) := by decide +kernel

private theorem vertex_step_rank_b27 : ∀ i : Fin 48, 0 < vertexRankValue (1296+i.val) → vertexRankValue (rotateValue (1296+i.val)) + 1 = vertexRankValue (1296+i.val) := by decide +kernel

private theorem vertex_step_rank_b28 : ∀ i : Fin 48, 0 < vertexRankValue (1344+i.val) → vertexRankValue (rotateValue (1344+i.val)) + 1 = vertexRankValue (1344+i.val) := by decide +kernel

private theorem vertex_step_rank_b29 : ∀ i : Fin 48, 0 < vertexRankValue (1392+i.val) → vertexRankValue (rotateValue (1392+i.val)) + 1 = vertexRankValue (1392+i.val) := by decide +kernel

private theorem vertex_step_rank_b30 : ∀ i : Fin 48, 0 < vertexRankValue (1440+i.val) → vertexRankValue (rotateValue (1440+i.val)) + 1 = vertexRankValue (1440+i.val) := by decide +kernel

private theorem vertex_step_rank_b31 : ∀ i : Fin 48, 0 < vertexRankValue (1488+i.val) → vertexRankValue (rotateValue (1488+i.val)) + 1 = vertexRankValue (1488+i.val) := by decide +kernel

private theorem vertex_step_rank_b32 : ∀ i : Fin 48, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) := by decide +kernel

private theorem vertex_step_rank_b33 : ∀ i : Fin 48, 0 < vertexRankValue (1584+i.val) → vertexRankValue (rotateValue (1584+i.val)) + 1 = vertexRankValue (1584+i.val) := by decide +kernel

private theorem vertex_step_rank_b34 : ∀ i : Fin 48, 0 < vertexRankValue (1632+i.val) → vertexRankValue (rotateValue (1632+i.val)) + 1 = vertexRankValue (1632+i.val) := by decide +kernel

private theorem vertex_step_rank_b35 : ∀ i : Fin 48, 0 < vertexRankValue (1680+i.val) → vertexRankValue (rotateValue (1680+i.val)) + 1 = vertexRankValue (1680+i.val) := by decide +kernel

private theorem vertex_step_rank_b36 : ∀ i : Fin 48, 0 < vertexRankValue (1728+i.val) → vertexRankValue (rotateValue (1728+i.val)) + 1 = vertexRankValue (1728+i.val) := by decide +kernel

private theorem vertex_step_rank_b37 : ∀ i : Fin 48, 0 < vertexRankValue (1776+i.val) → vertexRankValue (rotateValue (1776+i.val)) + 1 = vertexRankValue (1776+i.val) := by decide +kernel

private theorem vertex_step_rank_b38 : ∀ i : Fin 48, 0 < vertexRankValue (1824+i.val) → vertexRankValue (rotateValue (1824+i.val)) + 1 = vertexRankValue (1824+i.val) := by decide +kernel

private theorem vertex_step_rank_b39 : ∀ i : Fin 48, 0 < vertexRankValue (1872+i.val) → vertexRankValue (rotateValue (1872+i.val)) + 1 = vertexRankValue (1872+i.val) := by decide +kernel

private theorem vertex_step_rank_b40 : ∀ i : Fin 48, 0 < vertexRankValue (1920+i.val) → vertexRankValue (rotateValue (1920+i.val)) + 1 = vertexRankValue (1920+i.val) := by decide +kernel

private theorem vertex_step_rank_b41 : ∀ i : Fin 48, 0 < vertexRankValue (1968+i.val) → vertexRankValue (rotateValue (1968+i.val)) + 1 = vertexRankValue (1968+i.val) := by decide +kernel

private theorem vertex_step_rank_b42 : ∀ i : Fin 48, 0 < vertexRankValue (2016+i.val) → vertexRankValue (rotateValue (2016+i.val)) + 1 = vertexRankValue (2016+i.val) := by decide +kernel

private theorem vertex_step_rank_b43 : ∀ i : Fin 48, 0 < vertexRankValue (2064+i.val) → vertexRankValue (rotateValue (2064+i.val)) + 1 = vertexRankValue (2064+i.val) := by decide +kernel

private theorem vertex_step_rank_b44 : ∀ i : Fin 48, 0 < vertexRankValue (2112+i.val) → vertexRankValue (rotateValue (2112+i.val)) + 1 = vertexRankValue (2112+i.val) := by decide +kernel

private theorem vertex_step_rank_b45 : ∀ i : Fin 48, 0 < vertexRankValue (2160+i.val) → vertexRankValue (rotateValue (2160+i.val)) + 1 = vertexRankValue (2160+i.val) := by decide +kernel

private theorem vertex_step_rank_b46 : ∀ i : Fin 48, 0 < vertexRankValue (2208+i.val) → vertexRankValue (rotateValue (2208+i.val)) + 1 = vertexRankValue (2208+i.val) := by decide +kernel

private theorem vertex_step_rank_b47 : ∀ i : Fin 48, 0 < vertexRankValue (2256+i.val) → vertexRankValue (rotateValue (2256+i.val)) + 1 = vertexRankValue (2256+i.val) := by decide +kernel

private theorem vertex_step_rank_b48 : ∀ i : Fin 48, 0 < vertexRankValue (2304+i.val) → vertexRankValue (rotateValue (2304+i.val)) + 1 = vertexRankValue (2304+i.val) := by decide +kernel

private theorem vertex_step_rank_b49 : ∀ i : Fin 48, 0 < vertexRankValue (2352+i.val) → vertexRankValue (rotateValue (2352+i.val)) + 1 = vertexRankValue (2352+i.val) := by decide +kernel

private theorem vertex_step_rank_b50 : ∀ i : Fin 48, 0 < vertexRankValue (2400+i.val) → vertexRankValue (rotateValue (2400+i.val)) + 1 = vertexRankValue (2400+i.val) := by decide +kernel

private theorem vertex_step_rank_b51 : ∀ i : Fin 48, 0 < vertexRankValue (2448+i.val) → vertexRankValue (rotateValue (2448+i.val)) + 1 = vertexRankValue (2448+i.val) := by decide +kernel

private theorem vertex_step_rank_b52 : ∀ i : Fin 48, 0 < vertexRankValue (2496+i.val) → vertexRankValue (rotateValue (2496+i.val)) + 1 = vertexRankValue (2496+i.val) := by decide +kernel

private theorem vertex_step_rank_b53 : ∀ i : Fin 48, 0 < vertexRankValue (2544+i.val) → vertexRankValue (rotateValue (2544+i.val)) + 1 = vertexRankValue (2544+i.val) := by decide +kernel

private theorem vertex_step_rank_b54 : ∀ i : Fin 48, 0 < vertexRankValue (2592+i.val) → vertexRankValue (rotateValue (2592+i.val)) + 1 = vertexRankValue (2592+i.val) := by decide +kernel

private theorem vertex_step_rank_b55 : ∀ i : Fin 48, 0 < vertexRankValue (2640+i.val) → vertexRankValue (rotateValue (2640+i.val)) + 1 = vertexRankValue (2640+i.val) := by decide +kernel

private theorem vertex_step_rank_b56 : ∀ i : Fin 48, 0 < vertexRankValue (2688+i.val) → vertexRankValue (rotateValue (2688+i.val)) + 1 = vertexRankValue (2688+i.val) := by decide +kernel

private theorem vertex_step_rank_b57 : ∀ i : Fin 48, 0 < vertexRankValue (2736+i.val) → vertexRankValue (rotateValue (2736+i.val)) + 1 = vertexRankValue (2736+i.val) := by decide +kernel

private theorem vertex_step_rank_b58 : ∀ i : Fin 48, 0 < vertexRankValue (2784+i.val) → vertexRankValue (rotateValue (2784+i.val)) + 1 = vertexRankValue (2784+i.val) := by decide +kernel

private theorem vertex_step_rank_b59 : ∀ i : Fin 48, 0 < vertexRankValue (2832+i.val) → vertexRankValue (rotateValue (2832+i.val)) + 1 = vertexRankValue (2832+i.val) := by decide +kernel

private theorem vertex_step_rank_b60 : ∀ i : Fin 48, 0 < vertexRankValue (2880+i.val) → vertexRankValue (rotateValue (2880+i.val)) + 1 = vertexRankValue (2880+i.val) := by decide +kernel

private theorem vertex_step_rank_b61 : ∀ i : Fin 48, 0 < vertexRankValue (2928+i.val) → vertexRankValue (rotateValue (2928+i.val)) + 1 = vertexRankValue (2928+i.val) := by decide +kernel

private theorem vertex_step_rank_b62 : ∀ i : Fin 48, 0 < vertexRankValue (2976+i.val) → vertexRankValue (rotateValue (2976+i.val)) + 1 = vertexRankValue (2976+i.val) := by decide +kernel

private theorem vertex_step_rank_b63 : ∀ i : Fin 48, 0 < vertexRankValue (3024+i.val) → vertexRankValue (rotateValue (3024+i.val)) + 1 = vertexRankValue (3024+i.val) := by decide +kernel

private theorem vertex_step_rank_b64 : ∀ i : Fin 48, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) := by decide +kernel

private theorem vertex_step_rank_b65 : ∀ i : Fin 48, 0 < vertexRankValue (3120+i.val) → vertexRankValue (rotateValue (3120+i.val)) + 1 = vertexRankValue (3120+i.val) := by decide +kernel

private theorem vertex_step_rank_b66 : ∀ i : Fin 48, 0 < vertexRankValue (3168+i.val) → vertexRankValue (rotateValue (3168+i.val)) + 1 = vertexRankValue (3168+i.val) := by decide +kernel

private theorem vertex_step_rank_b67 : ∀ i : Fin 48, 0 < vertexRankValue (3216+i.val) → vertexRankValue (rotateValue (3216+i.val)) + 1 = vertexRankValue (3216+i.val) := by decide +kernel

private theorem vertex_step_rank_b68 : ∀ i : Fin 48, 0 < vertexRankValue (3264+i.val) → vertexRankValue (rotateValue (3264+i.val)) + 1 = vertexRankValue (3264+i.val) := by decide +kernel

private theorem vertex_step_rank_b69 : ∀ i : Fin 48, 0 < vertexRankValue (3312+i.val) → vertexRankValue (rotateValue (3312+i.val)) + 1 = vertexRankValue (3312+i.val) := by decide +kernel

private theorem vertex_step_rank_b70 : ∀ i : Fin 48, 0 < vertexRankValue (3360+i.val) → vertexRankValue (rotateValue (3360+i.val)) + 1 = vertexRankValue (3360+i.val) := by decide +kernel

private theorem vertex_step_rank_b71 : ∀ i : Fin 48, 0 < vertexRankValue (3408+i.val) → vertexRankValue (rotateValue (3408+i.val)) + 1 = vertexRankValue (3408+i.val) := by decide +kernel

private theorem vertex_step_rank_b72 : ∀ i : Fin 48, 0 < vertexRankValue (3456+i.val) → vertexRankValue (rotateValue (3456+i.val)) + 1 = vertexRankValue (3456+i.val) := by decide +kernel

private theorem vertex_step_rank_b73 : ∀ i : Fin 48, 0 < vertexRankValue (3504+i.val) → vertexRankValue (rotateValue (3504+i.val)) + 1 = vertexRankValue (3504+i.val) := by decide +kernel

private theorem vertex_step_rank_b74 : ∀ i : Fin 48, 0 < vertexRankValue (3552+i.val) → vertexRankValue (rotateValue (3552+i.val)) + 1 = vertexRankValue (3552+i.val) := by decide +kernel

private theorem vertex_step_rank_b75 : ∀ i : Fin 48, 0 < vertexRankValue (3600+i.val) → vertexRankValue (rotateValue (3600+i.val)) + 1 = vertexRankValue (3600+i.val) := by decide +kernel

private theorem vertex_step_rank_b76 : ∀ i : Fin 48, 0 < vertexRankValue (3648+i.val) → vertexRankValue (rotateValue (3648+i.val)) + 1 = vertexRankValue (3648+i.val) := by decide +kernel

private theorem vertex_step_rank_b77 : ∀ i : Fin 48, 0 < vertexRankValue (3696+i.val) → vertexRankValue (rotateValue (3696+i.val)) + 1 = vertexRankValue (3696+i.val) := by decide +kernel

private theorem vertex_step_rank_b78 : ∀ i : Fin 48, 0 < vertexRankValue (3744+i.val) → vertexRankValue (rotateValue (3744+i.val)) + 1 = vertexRankValue (3744+i.val) := by decide +kernel

private theorem vertex_step_rank_b79 : ∀ i : Fin 48, 0 < vertexRankValue (3792+i.val) → vertexRankValue (rotateValue (3792+i.val)) + 1 = vertexRankValue (3792+i.val) := by decide +kernel

private theorem vertex_step_rank_b80 : ∀ i : Fin 48, 0 < vertexRankValue (3840+i.val) → vertexRankValue (rotateValue (3840+i.val)) + 1 = vertexRankValue (3840+i.val) := by decide +kernel

private theorem vertex_step_rank_b81 : ∀ i : Fin 48, 0 < vertexRankValue (3888+i.val) → vertexRankValue (rotateValue (3888+i.val)) + 1 = vertexRankValue (3888+i.val) := by decide +kernel

private theorem vertex_step_rank_b82 : ∀ i : Fin 48, 0 < vertexRankValue (3936+i.val) → vertexRankValue (rotateValue (3936+i.val)) + 1 = vertexRankValue (3936+i.val) := by decide +kernel

private theorem vertex_step_rank_b83 : ∀ i : Fin 48, 0 < vertexRankValue (3984+i.val) → vertexRankValue (rotateValue (3984+i.val)) + 1 = vertexRankValue (3984+i.val) := by decide +kernel

private theorem vertex_step_rank_b84 : ∀ i : Fin 48, 0 < vertexRankValue (4032+i.val) → vertexRankValue (rotateValue (4032+i.val)) + 1 = vertexRankValue (4032+i.val) := by decide +kernel

private theorem vertex_step_rank_b85 : ∀ i : Fin 48, 0 < vertexRankValue (4080+i.val) → vertexRankValue (rotateValue (4080+i.val)) + 1 = vertexRankValue (4080+i.val) := by decide +kernel

private theorem vertex_step_rank_b86 : ∀ i : Fin 48, 0 < vertexRankValue (4128+i.val) → vertexRankValue (rotateValue (4128+i.val)) + 1 = vertexRankValue (4128+i.val) := by decide +kernel

private theorem vertex_step_rank_b87 : ∀ i : Fin 48, 0 < vertexRankValue (4176+i.val) → vertexRankValue (rotateValue (4176+i.val)) + 1 = vertexRankValue (4176+i.val) := by decide +kernel

private theorem vertex_step_rank_b88 : ∀ i : Fin 48, 0 < vertexRankValue (4224+i.val) → vertexRankValue (rotateValue (4224+i.val)) + 1 = vertexRankValue (4224+i.val) := by decide +kernel

private theorem vertex_step_rank_b89 : ∀ i : Fin 48, 0 < vertexRankValue (4272+i.val) → vertexRankValue (rotateValue (4272+i.val)) + 1 = vertexRankValue (4272+i.val) := by decide +kernel

private theorem vertex_step_rank_b90 : ∀ i : Fin 48, 0 < vertexRankValue (4320+i.val) → vertexRankValue (rotateValue (4320+i.val)) + 1 = vertexRankValue (4320+i.val) := by decide +kernel

private theorem vertex_step_rank_b91 : ∀ i : Fin 48, 0 < vertexRankValue (4368+i.val) → vertexRankValue (rotateValue (4368+i.val)) + 1 = vertexRankValue (4368+i.val) := by decide +kernel

private theorem vertex_step_rank_b92 : ∀ i : Fin 48, 0 < vertexRankValue (4416+i.val) → vertexRankValue (rotateValue (4416+i.val)) + 1 = vertexRankValue (4416+i.val) := by decide +kernel

private theorem vertex_step_rank_b93 : ∀ i : Fin 48, 0 < vertexRankValue (4464+i.val) → vertexRankValue (rotateValue (4464+i.val)) + 1 = vertexRankValue (4464+i.val) := by decide +kernel

private theorem vertex_step_rank_b94 : ∀ i : Fin 48, 0 < vertexRankValue (4512+i.val) → vertexRankValue (rotateValue (4512+i.val)) + 1 = vertexRankValue (4512+i.val) := by decide +kernel

private theorem vertex_step_rank_b95 : ∀ i : Fin 48, 0 < vertexRankValue (4560+i.val) → vertexRankValue (rotateValue (4560+i.val)) + 1 = vertexRankValue (4560+i.val) := by decide +kernel

private theorem vertex_step_rank_b96 : ∀ i : Fin 48, 0 < vertexRankValue (4608+i.val) → vertexRankValue (rotateValue (4608+i.val)) + 1 = vertexRankValue (4608+i.val) := by decide +kernel

private theorem vertex_step_rank_b97 : ∀ i : Fin 48, 0 < vertexRankValue (4656+i.val) → vertexRankValue (rotateValue (4656+i.val)) + 1 = vertexRankValue (4656+i.val) := by decide +kernel

private theorem vertex_step_rank_b98 : ∀ i : Fin 48, 0 < vertexRankValue (4704+i.val) → vertexRankValue (rotateValue (4704+i.val)) + 1 = vertexRankValue (4704+i.val) := by decide +kernel

private theorem vertex_step_rank_b99 : ∀ i : Fin 48, 0 < vertexRankValue (4752+i.val) → vertexRankValue (rotateValue (4752+i.val)) + 1 = vertexRankValue (4752+i.val) := by decide +kernel

private theorem vertex_step_rank_b100 : ∀ i : Fin 48, 0 < vertexRankValue (4800+i.val) → vertexRankValue (rotateValue (4800+i.val)) + 1 = vertexRankValue (4800+i.val) := by decide +kernel

private theorem vertex_step_rank_b101 : ∀ i : Fin 48, 0 < vertexRankValue (4848+i.val) → vertexRankValue (rotateValue (4848+i.val)) + 1 = vertexRankValue (4848+i.val) := by decide +kernel

private theorem vertex_step_rank_b102 : ∀ i : Fin 48, 0 < vertexRankValue (4896+i.val) → vertexRankValue (rotateValue (4896+i.val)) + 1 = vertexRankValue (4896+i.val) := by decide +kernel

private theorem vertex_step_rank_b103 : ∀ i : Fin 48, 0 < vertexRankValue (4944+i.val) → vertexRankValue (rotateValue (4944+i.val)) + 1 = vertexRankValue (4944+i.val) := by decide +kernel

private theorem vertex_step_rank_b104 : ∀ i : Fin 48, 0 < vertexRankValue (4992+i.val) → vertexRankValue (rotateValue (4992+i.val)) + 1 = vertexRankValue (4992+i.val) := by decide +kernel

private theorem vertex_step_rank_b105 : ∀ i : Fin 48, 0 < vertexRankValue (5040+i.val) → vertexRankValue (rotateValue (5040+i.val)) + 1 = vertexRankValue (5040+i.val) := by decide +kernel

private theorem vertex_step_rank_b106 : ∀ i : Fin 48, 0 < vertexRankValue (5088+i.val) → vertexRankValue (rotateValue (5088+i.val)) + 1 = vertexRankValue (5088+i.val) := by decide +kernel

private theorem vertex_step_rank_b107 : ∀ i : Fin 48, 0 < vertexRankValue (5136+i.val) → vertexRankValue (rotateValue (5136+i.val)) + 1 = vertexRankValue (5136+i.val) := by decide +kernel

private theorem vertex_step_rank_b108 : ∀ i : Fin 48, 0 < vertexRankValue (5184+i.val) → vertexRankValue (rotateValue (5184+i.val)) + 1 = vertexRankValue (5184+i.val) := by decide +kernel

private theorem vertex_step_rank_b109 : ∀ i : Fin 32, 0 < vertexRankValue (5232+i.val) → vertexRankValue (rotateValue (5232+i.val)) + 1 = vertexRankValue (5232+i.val) := by decide +kernel

private theorem vertex_step_rank_n0_0 : ∀ i : Fin 96, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 48 48 vertex_step_rank_b0 vertex_step_rank_b1

private theorem vertex_step_rank_n0_1 : ∀ i : Fin 96, 0 < vertexRankValue (96+i.val) → vertexRankValue (rotateValue (96+i.val)) + 1 = vertexRankValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 96 48 48 vertex_step_rank_b2 vertex_step_rank_b3

private theorem vertex_step_rank_n0_2 : ∀ i : Fin 96, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 192 48 48 vertex_step_rank_b4 vertex_step_rank_b5

private theorem vertex_step_rank_n0_3 : ∀ i : Fin 96, 0 < vertexRankValue (288+i.val) → vertexRankValue (rotateValue (288+i.val)) + 1 = vertexRankValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 288 48 48 vertex_step_rank_b6 vertex_step_rank_b7

private theorem vertex_step_rank_n0_4 : ∀ i : Fin 96, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 384 48 48 vertex_step_rank_b8 vertex_step_rank_b9

private theorem vertex_step_rank_n0_5 : ∀ i : Fin 96, 0 < vertexRankValue (480+i.val) → vertexRankValue (rotateValue (480+i.val)) + 1 = vertexRankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 480 48 48 vertex_step_rank_b10 vertex_step_rank_b11

private theorem vertex_step_rank_n0_6 : ∀ i : Fin 96, 0 < vertexRankValue (576+i.val) → vertexRankValue (rotateValue (576+i.val)) + 1 = vertexRankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 576 48 48 vertex_step_rank_b12 vertex_step_rank_b13

private theorem vertex_step_rank_n0_7 : ∀ i : Fin 96, 0 < vertexRankValue (672+i.val) → vertexRankValue (rotateValue (672+i.val)) + 1 = vertexRankValue (672+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 672 48 48 vertex_step_rank_b14 vertex_step_rank_b15

private theorem vertex_step_rank_n0_8 : ∀ i : Fin 96, 0 < vertexRankValue (768+i.val) → vertexRankValue (rotateValue (768+i.val)) + 1 = vertexRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 768 48 48 vertex_step_rank_b16 vertex_step_rank_b17

private theorem vertex_step_rank_n0_9 : ∀ i : Fin 96, 0 < vertexRankValue (864+i.val) → vertexRankValue (rotateValue (864+i.val)) + 1 = vertexRankValue (864+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 864 48 48 vertex_step_rank_b18 vertex_step_rank_b19

private theorem vertex_step_rank_n0_10 : ∀ i : Fin 96, 0 < vertexRankValue (960+i.val) → vertexRankValue (rotateValue (960+i.val)) + 1 = vertexRankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 960 48 48 vertex_step_rank_b20 vertex_step_rank_b21

private theorem vertex_step_rank_n0_11 : ∀ i : Fin 96, 0 < vertexRankValue (1056+i.val) → vertexRankValue (rotateValue (1056+i.val)) + 1 = vertexRankValue (1056+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1056 48 48 vertex_step_rank_b22 vertex_step_rank_b23

private theorem vertex_step_rank_n0_12 : ∀ i : Fin 96, 0 < vertexRankValue (1152+i.val) → vertexRankValue (rotateValue (1152+i.val)) + 1 = vertexRankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1152 48 48 vertex_step_rank_b24 vertex_step_rank_b25

private theorem vertex_step_rank_n0_13 : ∀ i : Fin 96, 0 < vertexRankValue (1248+i.val) → vertexRankValue (rotateValue (1248+i.val)) + 1 = vertexRankValue (1248+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1248 48 48 vertex_step_rank_b26 vertex_step_rank_b27

private theorem vertex_step_rank_n0_14 : ∀ i : Fin 96, 0 < vertexRankValue (1344+i.val) → vertexRankValue (rotateValue (1344+i.val)) + 1 = vertexRankValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1344 48 48 vertex_step_rank_b28 vertex_step_rank_b29

private theorem vertex_step_rank_n0_15 : ∀ i : Fin 96, 0 < vertexRankValue (1440+i.val) → vertexRankValue (rotateValue (1440+i.val)) + 1 = vertexRankValue (1440+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1440 48 48 vertex_step_rank_b30 vertex_step_rank_b31

private theorem vertex_step_rank_n0_16 : ∀ i : Fin 96, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1536 48 48 vertex_step_rank_b32 vertex_step_rank_b33

private theorem vertex_step_rank_n0_17 : ∀ i : Fin 96, 0 < vertexRankValue (1632+i.val) → vertexRankValue (rotateValue (1632+i.val)) + 1 = vertexRankValue (1632+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1632 48 48 vertex_step_rank_b34 vertex_step_rank_b35

private theorem vertex_step_rank_n0_18 : ∀ i : Fin 96, 0 < vertexRankValue (1728+i.val) → vertexRankValue (rotateValue (1728+i.val)) + 1 = vertexRankValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1728 48 48 vertex_step_rank_b36 vertex_step_rank_b37

private theorem vertex_step_rank_n0_19 : ∀ i : Fin 96, 0 < vertexRankValue (1824+i.val) → vertexRankValue (rotateValue (1824+i.val)) + 1 = vertexRankValue (1824+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1824 48 48 vertex_step_rank_b38 vertex_step_rank_b39

private theorem vertex_step_rank_n0_20 : ∀ i : Fin 96, 0 < vertexRankValue (1920+i.val) → vertexRankValue (rotateValue (1920+i.val)) + 1 = vertexRankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1920 48 48 vertex_step_rank_b40 vertex_step_rank_b41

private theorem vertex_step_rank_n0_21 : ∀ i : Fin 96, 0 < vertexRankValue (2016+i.val) → vertexRankValue (rotateValue (2016+i.val)) + 1 = vertexRankValue (2016+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2016 48 48 vertex_step_rank_b42 vertex_step_rank_b43

private theorem vertex_step_rank_n0_22 : ∀ i : Fin 96, 0 < vertexRankValue (2112+i.val) → vertexRankValue (rotateValue (2112+i.val)) + 1 = vertexRankValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2112 48 48 vertex_step_rank_b44 vertex_step_rank_b45

private theorem vertex_step_rank_n0_23 : ∀ i : Fin 96, 0 < vertexRankValue (2208+i.val) → vertexRankValue (rotateValue (2208+i.val)) + 1 = vertexRankValue (2208+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2208 48 48 vertex_step_rank_b46 vertex_step_rank_b47

private theorem vertex_step_rank_n0_24 : ∀ i : Fin 96, 0 < vertexRankValue (2304+i.val) → vertexRankValue (rotateValue (2304+i.val)) + 1 = vertexRankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2304 48 48 vertex_step_rank_b48 vertex_step_rank_b49

private theorem vertex_step_rank_n0_25 : ∀ i : Fin 96, 0 < vertexRankValue (2400+i.val) → vertexRankValue (rotateValue (2400+i.val)) + 1 = vertexRankValue (2400+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2400 48 48 vertex_step_rank_b50 vertex_step_rank_b51

private theorem vertex_step_rank_n0_26 : ∀ i : Fin 96, 0 < vertexRankValue (2496+i.val) → vertexRankValue (rotateValue (2496+i.val)) + 1 = vertexRankValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2496 48 48 vertex_step_rank_b52 vertex_step_rank_b53

private theorem vertex_step_rank_n0_27 : ∀ i : Fin 96, 0 < vertexRankValue (2592+i.val) → vertexRankValue (rotateValue (2592+i.val)) + 1 = vertexRankValue (2592+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2592 48 48 vertex_step_rank_b54 vertex_step_rank_b55

private theorem vertex_step_rank_n0_28 : ∀ i : Fin 96, 0 < vertexRankValue (2688+i.val) → vertexRankValue (rotateValue (2688+i.val)) + 1 = vertexRankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2688 48 48 vertex_step_rank_b56 vertex_step_rank_b57

private theorem vertex_step_rank_n0_29 : ∀ i : Fin 96, 0 < vertexRankValue (2784+i.val) → vertexRankValue (rotateValue (2784+i.val)) + 1 = vertexRankValue (2784+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2784 48 48 vertex_step_rank_b58 vertex_step_rank_b59

private theorem vertex_step_rank_n0_30 : ∀ i : Fin 96, 0 < vertexRankValue (2880+i.val) → vertexRankValue (rotateValue (2880+i.val)) + 1 = vertexRankValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2880 48 48 vertex_step_rank_b60 vertex_step_rank_b61

private theorem vertex_step_rank_n0_31 : ∀ i : Fin 96, 0 < vertexRankValue (2976+i.val) → vertexRankValue (rotateValue (2976+i.val)) + 1 = vertexRankValue (2976+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2976 48 48 vertex_step_rank_b62 vertex_step_rank_b63

private theorem vertex_step_rank_n0_32 : ∀ i : Fin 96, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 48 48 vertex_step_rank_b64 vertex_step_rank_b65

private theorem vertex_step_rank_n0_33 : ∀ i : Fin 96, 0 < vertexRankValue (3168+i.val) → vertexRankValue (rotateValue (3168+i.val)) + 1 = vertexRankValue (3168+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3168 48 48 vertex_step_rank_b66 vertex_step_rank_b67

private theorem vertex_step_rank_n0_34 : ∀ i : Fin 96, 0 < vertexRankValue (3264+i.val) → vertexRankValue (rotateValue (3264+i.val)) + 1 = vertexRankValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3264 48 48 vertex_step_rank_b68 vertex_step_rank_b69

private theorem vertex_step_rank_n0_35 : ∀ i : Fin 96, 0 < vertexRankValue (3360+i.val) → vertexRankValue (rotateValue (3360+i.val)) + 1 = vertexRankValue (3360+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3360 48 48 vertex_step_rank_b70 vertex_step_rank_b71

private theorem vertex_step_rank_n0_36 : ∀ i : Fin 96, 0 < vertexRankValue (3456+i.val) → vertexRankValue (rotateValue (3456+i.val)) + 1 = vertexRankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3456 48 48 vertex_step_rank_b72 vertex_step_rank_b73

private theorem vertex_step_rank_n0_37 : ∀ i : Fin 96, 0 < vertexRankValue (3552+i.val) → vertexRankValue (rotateValue (3552+i.val)) + 1 = vertexRankValue (3552+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3552 48 48 vertex_step_rank_b74 vertex_step_rank_b75

private theorem vertex_step_rank_n0_38 : ∀ i : Fin 96, 0 < vertexRankValue (3648+i.val) → vertexRankValue (rotateValue (3648+i.val)) + 1 = vertexRankValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3648 48 48 vertex_step_rank_b76 vertex_step_rank_b77

private theorem vertex_step_rank_n0_39 : ∀ i : Fin 96, 0 < vertexRankValue (3744+i.val) → vertexRankValue (rotateValue (3744+i.val)) + 1 = vertexRankValue (3744+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3744 48 48 vertex_step_rank_b78 vertex_step_rank_b79

private theorem vertex_step_rank_n0_40 : ∀ i : Fin 96, 0 < vertexRankValue (3840+i.val) → vertexRankValue (rotateValue (3840+i.val)) + 1 = vertexRankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3840 48 48 vertex_step_rank_b80 vertex_step_rank_b81

private theorem vertex_step_rank_n0_41 : ∀ i : Fin 96, 0 < vertexRankValue (3936+i.val) → vertexRankValue (rotateValue (3936+i.val)) + 1 = vertexRankValue (3936+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3936 48 48 vertex_step_rank_b82 vertex_step_rank_b83

private theorem vertex_step_rank_n0_42 : ∀ i : Fin 96, 0 < vertexRankValue (4032+i.val) → vertexRankValue (rotateValue (4032+i.val)) + 1 = vertexRankValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4032 48 48 vertex_step_rank_b84 vertex_step_rank_b85

private theorem vertex_step_rank_n0_43 : ∀ i : Fin 96, 0 < vertexRankValue (4128+i.val) → vertexRankValue (rotateValue (4128+i.val)) + 1 = vertexRankValue (4128+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4128 48 48 vertex_step_rank_b86 vertex_step_rank_b87

private theorem vertex_step_rank_n0_44 : ∀ i : Fin 96, 0 < vertexRankValue (4224+i.val) → vertexRankValue (rotateValue (4224+i.val)) + 1 = vertexRankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4224 48 48 vertex_step_rank_b88 vertex_step_rank_b89

private theorem vertex_step_rank_n0_45 : ∀ i : Fin 96, 0 < vertexRankValue (4320+i.val) → vertexRankValue (rotateValue (4320+i.val)) + 1 = vertexRankValue (4320+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4320 48 48 vertex_step_rank_b90 vertex_step_rank_b91

private theorem vertex_step_rank_n0_46 : ∀ i : Fin 96, 0 < vertexRankValue (4416+i.val) → vertexRankValue (rotateValue (4416+i.val)) + 1 = vertexRankValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4416 48 48 vertex_step_rank_b92 vertex_step_rank_b93

private theorem vertex_step_rank_n0_47 : ∀ i : Fin 96, 0 < vertexRankValue (4512+i.val) → vertexRankValue (rotateValue (4512+i.val)) + 1 = vertexRankValue (4512+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4512 48 48 vertex_step_rank_b94 vertex_step_rank_b95

private theorem vertex_step_rank_n0_48 : ∀ i : Fin 96, 0 < vertexRankValue (4608+i.val) → vertexRankValue (rotateValue (4608+i.val)) + 1 = vertexRankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4608 48 48 vertex_step_rank_b96 vertex_step_rank_b97

private theorem vertex_step_rank_n0_49 : ∀ i : Fin 96, 0 < vertexRankValue (4704+i.val) → vertexRankValue (rotateValue (4704+i.val)) + 1 = vertexRankValue (4704+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4704 48 48 vertex_step_rank_b98 vertex_step_rank_b99

private theorem vertex_step_rank_n0_50 : ∀ i : Fin 96, 0 < vertexRankValue (4800+i.val) → vertexRankValue (rotateValue (4800+i.val)) + 1 = vertexRankValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4800 48 48 vertex_step_rank_b100 vertex_step_rank_b101

private theorem vertex_step_rank_n0_51 : ∀ i : Fin 96, 0 < vertexRankValue (4896+i.val) → vertexRankValue (rotateValue (4896+i.val)) + 1 = vertexRankValue (4896+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4896 48 48 vertex_step_rank_b102 vertex_step_rank_b103

private theorem vertex_step_rank_n0_52 : ∀ i : Fin 96, 0 < vertexRankValue (4992+i.val) → vertexRankValue (rotateValue (4992+i.val)) + 1 = vertexRankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4992 48 48 vertex_step_rank_b104 vertex_step_rank_b105

private theorem vertex_step_rank_n0_53 : ∀ i : Fin 96, 0 < vertexRankValue (5088+i.val) → vertexRankValue (rotateValue (5088+i.val)) + 1 = vertexRankValue (5088+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 5088 48 48 vertex_step_rank_b106 vertex_step_rank_b107

private theorem vertex_step_rank_n0_54 : ∀ i : Fin 80, 0 < vertexRankValue (5184+i.val) → vertexRankValue (rotateValue (5184+i.val)) + 1 = vertexRankValue (5184+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 5184 48 32 vertex_step_rank_b108 vertex_step_rank_b109

private theorem vertex_step_rank_n1_0 : ∀ i : Fin 192, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 96 96 vertex_step_rank_n0_0 vertex_step_rank_n0_1

private theorem vertex_step_rank_n1_1 : ∀ i : Fin 192, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 192 96 96 vertex_step_rank_n0_2 vertex_step_rank_n0_3

private theorem vertex_step_rank_n1_2 : ∀ i : Fin 192, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 384 96 96 vertex_step_rank_n0_4 vertex_step_rank_n0_5

private theorem vertex_step_rank_n1_3 : ∀ i : Fin 192, 0 < vertexRankValue (576+i.val) → vertexRankValue (rotateValue (576+i.val)) + 1 = vertexRankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 576 96 96 vertex_step_rank_n0_6 vertex_step_rank_n0_7

private theorem vertex_step_rank_n1_4 : ∀ i : Fin 192, 0 < vertexRankValue (768+i.val) → vertexRankValue (rotateValue (768+i.val)) + 1 = vertexRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 768 96 96 vertex_step_rank_n0_8 vertex_step_rank_n0_9

private theorem vertex_step_rank_n1_5 : ∀ i : Fin 192, 0 < vertexRankValue (960+i.val) → vertexRankValue (rotateValue (960+i.val)) + 1 = vertexRankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 960 96 96 vertex_step_rank_n0_10 vertex_step_rank_n0_11

private theorem vertex_step_rank_n1_6 : ∀ i : Fin 192, 0 < vertexRankValue (1152+i.val) → vertexRankValue (rotateValue (1152+i.val)) + 1 = vertexRankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1152 96 96 vertex_step_rank_n0_12 vertex_step_rank_n0_13

private theorem vertex_step_rank_n1_7 : ∀ i : Fin 192, 0 < vertexRankValue (1344+i.val) → vertexRankValue (rotateValue (1344+i.val)) + 1 = vertexRankValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1344 96 96 vertex_step_rank_n0_14 vertex_step_rank_n0_15

private theorem vertex_step_rank_n1_8 : ∀ i : Fin 192, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1536 96 96 vertex_step_rank_n0_16 vertex_step_rank_n0_17

private theorem vertex_step_rank_n1_9 : ∀ i : Fin 192, 0 < vertexRankValue (1728+i.val) → vertexRankValue (rotateValue (1728+i.val)) + 1 = vertexRankValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1728 96 96 vertex_step_rank_n0_18 vertex_step_rank_n0_19

private theorem vertex_step_rank_n1_10 : ∀ i : Fin 192, 0 < vertexRankValue (1920+i.val) → vertexRankValue (rotateValue (1920+i.val)) + 1 = vertexRankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1920 96 96 vertex_step_rank_n0_20 vertex_step_rank_n0_21

private theorem vertex_step_rank_n1_11 : ∀ i : Fin 192, 0 < vertexRankValue (2112+i.val) → vertexRankValue (rotateValue (2112+i.val)) + 1 = vertexRankValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2112 96 96 vertex_step_rank_n0_22 vertex_step_rank_n0_23

private theorem vertex_step_rank_n1_12 : ∀ i : Fin 192, 0 < vertexRankValue (2304+i.val) → vertexRankValue (rotateValue (2304+i.val)) + 1 = vertexRankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2304 96 96 vertex_step_rank_n0_24 vertex_step_rank_n0_25

private theorem vertex_step_rank_n1_13 : ∀ i : Fin 192, 0 < vertexRankValue (2496+i.val) → vertexRankValue (rotateValue (2496+i.val)) + 1 = vertexRankValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2496 96 96 vertex_step_rank_n0_26 vertex_step_rank_n0_27

private theorem vertex_step_rank_n1_14 : ∀ i : Fin 192, 0 < vertexRankValue (2688+i.val) → vertexRankValue (rotateValue (2688+i.val)) + 1 = vertexRankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2688 96 96 vertex_step_rank_n0_28 vertex_step_rank_n0_29

private theorem vertex_step_rank_n1_15 : ∀ i : Fin 192, 0 < vertexRankValue (2880+i.val) → vertexRankValue (rotateValue (2880+i.val)) + 1 = vertexRankValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2880 96 96 vertex_step_rank_n0_30 vertex_step_rank_n0_31

private theorem vertex_step_rank_n1_16 : ∀ i : Fin 192, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 96 96 vertex_step_rank_n0_32 vertex_step_rank_n0_33

private theorem vertex_step_rank_n1_17 : ∀ i : Fin 192, 0 < vertexRankValue (3264+i.val) → vertexRankValue (rotateValue (3264+i.val)) + 1 = vertexRankValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3264 96 96 vertex_step_rank_n0_34 vertex_step_rank_n0_35

private theorem vertex_step_rank_n1_18 : ∀ i : Fin 192, 0 < vertexRankValue (3456+i.val) → vertexRankValue (rotateValue (3456+i.val)) + 1 = vertexRankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3456 96 96 vertex_step_rank_n0_36 vertex_step_rank_n0_37

private theorem vertex_step_rank_n1_19 : ∀ i : Fin 192, 0 < vertexRankValue (3648+i.val) → vertexRankValue (rotateValue (3648+i.val)) + 1 = vertexRankValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3648 96 96 vertex_step_rank_n0_38 vertex_step_rank_n0_39

private theorem vertex_step_rank_n1_20 : ∀ i : Fin 192, 0 < vertexRankValue (3840+i.val) → vertexRankValue (rotateValue (3840+i.val)) + 1 = vertexRankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3840 96 96 vertex_step_rank_n0_40 vertex_step_rank_n0_41

private theorem vertex_step_rank_n1_21 : ∀ i : Fin 192, 0 < vertexRankValue (4032+i.val) → vertexRankValue (rotateValue (4032+i.val)) + 1 = vertexRankValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4032 96 96 vertex_step_rank_n0_42 vertex_step_rank_n0_43

private theorem vertex_step_rank_n1_22 : ∀ i : Fin 192, 0 < vertexRankValue (4224+i.val) → vertexRankValue (rotateValue (4224+i.val)) + 1 = vertexRankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4224 96 96 vertex_step_rank_n0_44 vertex_step_rank_n0_45

private theorem vertex_step_rank_n1_23 : ∀ i : Fin 192, 0 < vertexRankValue (4416+i.val) → vertexRankValue (rotateValue (4416+i.val)) + 1 = vertexRankValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4416 96 96 vertex_step_rank_n0_46 vertex_step_rank_n0_47

private theorem vertex_step_rank_n1_24 : ∀ i : Fin 192, 0 < vertexRankValue (4608+i.val) → vertexRankValue (rotateValue (4608+i.val)) + 1 = vertexRankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4608 96 96 vertex_step_rank_n0_48 vertex_step_rank_n0_49

private theorem vertex_step_rank_n1_25 : ∀ i : Fin 192, 0 < vertexRankValue (4800+i.val) → vertexRankValue (rotateValue (4800+i.val)) + 1 = vertexRankValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4800 96 96 vertex_step_rank_n0_50 vertex_step_rank_n0_51

private theorem vertex_step_rank_n1_26 : ∀ i : Fin 192, 0 < vertexRankValue (4992+i.val) → vertexRankValue (rotateValue (4992+i.val)) + 1 = vertexRankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4992 96 96 vertex_step_rank_n0_52 vertex_step_rank_n0_53

private theorem vertex_step_rank_n2_0 : ∀ i : Fin 384, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 192 192 vertex_step_rank_n1_0 vertex_step_rank_n1_1

private theorem vertex_step_rank_n2_1 : ∀ i : Fin 384, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 384 192 192 vertex_step_rank_n1_2 vertex_step_rank_n1_3

private theorem vertex_step_rank_n2_2 : ∀ i : Fin 384, 0 < vertexRankValue (768+i.val) → vertexRankValue (rotateValue (768+i.val)) + 1 = vertexRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 768 192 192 vertex_step_rank_n1_4 vertex_step_rank_n1_5

private theorem vertex_step_rank_n2_3 : ∀ i : Fin 384, 0 < vertexRankValue (1152+i.val) → vertexRankValue (rotateValue (1152+i.val)) + 1 = vertexRankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1152 192 192 vertex_step_rank_n1_6 vertex_step_rank_n1_7

private theorem vertex_step_rank_n2_4 : ∀ i : Fin 384, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1536 192 192 vertex_step_rank_n1_8 vertex_step_rank_n1_9

private theorem vertex_step_rank_n2_5 : ∀ i : Fin 384, 0 < vertexRankValue (1920+i.val) → vertexRankValue (rotateValue (1920+i.val)) + 1 = vertexRankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1920 192 192 vertex_step_rank_n1_10 vertex_step_rank_n1_11

private theorem vertex_step_rank_n2_6 : ∀ i : Fin 384, 0 < vertexRankValue (2304+i.val) → vertexRankValue (rotateValue (2304+i.val)) + 1 = vertexRankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2304 192 192 vertex_step_rank_n1_12 vertex_step_rank_n1_13

private theorem vertex_step_rank_n2_7 : ∀ i : Fin 384, 0 < vertexRankValue (2688+i.val) → vertexRankValue (rotateValue (2688+i.val)) + 1 = vertexRankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2688 192 192 vertex_step_rank_n1_14 vertex_step_rank_n1_15

private theorem vertex_step_rank_n2_8 : ∀ i : Fin 384, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 192 192 vertex_step_rank_n1_16 vertex_step_rank_n1_17

private theorem vertex_step_rank_n2_9 : ∀ i : Fin 384, 0 < vertexRankValue (3456+i.val) → vertexRankValue (rotateValue (3456+i.val)) + 1 = vertexRankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3456 192 192 vertex_step_rank_n1_18 vertex_step_rank_n1_19

private theorem vertex_step_rank_n2_10 : ∀ i : Fin 384, 0 < vertexRankValue (3840+i.val) → vertexRankValue (rotateValue (3840+i.val)) + 1 = vertexRankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3840 192 192 vertex_step_rank_n1_20 vertex_step_rank_n1_21

private theorem vertex_step_rank_n2_11 : ∀ i : Fin 384, 0 < vertexRankValue (4224+i.val) → vertexRankValue (rotateValue (4224+i.val)) + 1 = vertexRankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4224 192 192 vertex_step_rank_n1_22 vertex_step_rank_n1_23

private theorem vertex_step_rank_n2_12 : ∀ i : Fin 384, 0 < vertexRankValue (4608+i.val) → vertexRankValue (rotateValue (4608+i.val)) + 1 = vertexRankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4608 192 192 vertex_step_rank_n1_24 vertex_step_rank_n1_25

private theorem vertex_step_rank_n2_13 : ∀ i : Fin 272, 0 < vertexRankValue (4992+i.val) → vertexRankValue (rotateValue (4992+i.val)) + 1 = vertexRankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4992 192 80 vertex_step_rank_n1_26 vertex_step_rank_n0_54

private theorem vertex_step_rank_n3_0 : ∀ i : Fin 768, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 384 384 vertex_step_rank_n2_0 vertex_step_rank_n2_1

private theorem vertex_step_rank_n3_1 : ∀ i : Fin 768, 0 < vertexRankValue (768+i.val) → vertexRankValue (rotateValue (768+i.val)) + 1 = vertexRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 768 384 384 vertex_step_rank_n2_2 vertex_step_rank_n2_3

private theorem vertex_step_rank_n3_2 : ∀ i : Fin 768, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1536 384 384 vertex_step_rank_n2_4 vertex_step_rank_n2_5

private theorem vertex_step_rank_n3_3 : ∀ i : Fin 768, 0 < vertexRankValue (2304+i.val) → vertexRankValue (rotateValue (2304+i.val)) + 1 = vertexRankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 2304 384 384 vertex_step_rank_n2_6 vertex_step_rank_n2_7

private theorem vertex_step_rank_n3_4 : ∀ i : Fin 768, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 384 384 vertex_step_rank_n2_8 vertex_step_rank_n2_9

private theorem vertex_step_rank_n3_5 : ∀ i : Fin 768, 0 < vertexRankValue (3840+i.val) → vertexRankValue (rotateValue (3840+i.val)) + 1 = vertexRankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3840 384 384 vertex_step_rank_n2_10 vertex_step_rank_n2_11

private theorem vertex_step_rank_n3_6 : ∀ i : Fin 656, 0 < vertexRankValue (4608+i.val) → vertexRankValue (rotateValue (4608+i.val)) + 1 = vertexRankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 4608 384 272 vertex_step_rank_n2_12 vertex_step_rank_n2_13

private theorem vertex_step_rank_n4_0 : ∀ i : Fin 1536, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 768 768 vertex_step_rank_n3_0 vertex_step_rank_n3_1

private theorem vertex_step_rank_n4_1 : ∀ i : Fin 1536, 0 < vertexRankValue (1536+i.val) → vertexRankValue (rotateValue (1536+i.val)) + 1 = vertexRankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 1536 768 768 vertex_step_rank_n3_2 vertex_step_rank_n3_3

private theorem vertex_step_rank_n4_2 : ∀ i : Fin 1536, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 768 768 vertex_step_rank_n3_4 vertex_step_rank_n3_5

private theorem vertex_step_rank_n5_0 : ∀ i : Fin 3072, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 1536 1536 vertex_step_rank_n4_0 vertex_step_rank_n4_1

private theorem vertex_step_rank_n5_1 : ∀ i : Fin 2192, 0 < vertexRankValue (3072+i.val) → vertexRankValue (rotateValue (3072+i.val)) + 1 = vertexRankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 3072 1536 656 vertex_step_rank_n4_2 vertex_step_rank_n3_6

private theorem vertex_step_rank_n6_0 : ∀ i : Fin 5264, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 3072 2192 vertex_step_rank_n5_0 vertex_step_rank_n5_1

theorem vertex_step_rank : ∀ i : Fin 5264, 0 < vertexRankValue i.val → vertexRankValue (rotateValue i.val) + 1 = vertexRankValue i.val := by
  simpa only [Nat.zero_add] using vertex_step_rank_n6_0

end PlanarHom.ColoringMacroFaces.FanFramed
