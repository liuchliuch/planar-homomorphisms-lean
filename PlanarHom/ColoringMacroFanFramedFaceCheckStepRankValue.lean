import PlanarHom.ColoringMacroFanFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem step_rank_value_b0 : ∀ i : Fin 48, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) := by decide +kernel

private theorem step_rank_value_b1 : ∀ i : Fin 48, 0 < rankValue (48+i.val) → rankValue (nextValue (48+i.val)) + 1 = rankValue (48+i.val) := by decide +kernel

private theorem step_rank_value_b2 : ∀ i : Fin 48, 0 < rankValue (96+i.val) → rankValue (nextValue (96+i.val)) + 1 = rankValue (96+i.val) := by decide +kernel

private theorem step_rank_value_b3 : ∀ i : Fin 48, 0 < rankValue (144+i.val) → rankValue (nextValue (144+i.val)) + 1 = rankValue (144+i.val) := by decide +kernel

private theorem step_rank_value_b4 : ∀ i : Fin 48, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) := by decide +kernel

private theorem step_rank_value_b5 : ∀ i : Fin 48, 0 < rankValue (240+i.val) → rankValue (nextValue (240+i.val)) + 1 = rankValue (240+i.val) := by decide +kernel

private theorem step_rank_value_b6 : ∀ i : Fin 48, 0 < rankValue (288+i.val) → rankValue (nextValue (288+i.val)) + 1 = rankValue (288+i.val) := by decide +kernel

private theorem step_rank_value_b7 : ∀ i : Fin 48, 0 < rankValue (336+i.val) → rankValue (nextValue (336+i.val)) + 1 = rankValue (336+i.val) := by decide +kernel

private theorem step_rank_value_b8 : ∀ i : Fin 48, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) := by decide +kernel

private theorem step_rank_value_b9 : ∀ i : Fin 48, 0 < rankValue (432+i.val) → rankValue (nextValue (432+i.val)) + 1 = rankValue (432+i.val) := by decide +kernel

private theorem step_rank_value_b10 : ∀ i : Fin 48, 0 < rankValue (480+i.val) → rankValue (nextValue (480+i.val)) + 1 = rankValue (480+i.val) := by decide +kernel

private theorem step_rank_value_b11 : ∀ i : Fin 48, 0 < rankValue (528+i.val) → rankValue (nextValue (528+i.val)) + 1 = rankValue (528+i.val) := by decide +kernel

private theorem step_rank_value_b12 : ∀ i : Fin 48, 0 < rankValue (576+i.val) → rankValue (nextValue (576+i.val)) + 1 = rankValue (576+i.val) := by decide +kernel

private theorem step_rank_value_b13 : ∀ i : Fin 48, 0 < rankValue (624+i.val) → rankValue (nextValue (624+i.val)) + 1 = rankValue (624+i.val) := by decide +kernel

private theorem step_rank_value_b14 : ∀ i : Fin 48, 0 < rankValue (672+i.val) → rankValue (nextValue (672+i.val)) + 1 = rankValue (672+i.val) := by decide +kernel

private theorem step_rank_value_b15 : ∀ i : Fin 48, 0 < rankValue (720+i.val) → rankValue (nextValue (720+i.val)) + 1 = rankValue (720+i.val) := by decide +kernel

private theorem step_rank_value_b16 : ∀ i : Fin 48, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) := by decide +kernel

private theorem step_rank_value_b17 : ∀ i : Fin 48, 0 < rankValue (816+i.val) → rankValue (nextValue (816+i.val)) + 1 = rankValue (816+i.val) := by decide +kernel

private theorem step_rank_value_b18 : ∀ i : Fin 48, 0 < rankValue (864+i.val) → rankValue (nextValue (864+i.val)) + 1 = rankValue (864+i.val) := by decide +kernel

private theorem step_rank_value_b19 : ∀ i : Fin 48, 0 < rankValue (912+i.val) → rankValue (nextValue (912+i.val)) + 1 = rankValue (912+i.val) := by decide +kernel

private theorem step_rank_value_b20 : ∀ i : Fin 48, 0 < rankValue (960+i.val) → rankValue (nextValue (960+i.val)) + 1 = rankValue (960+i.val) := by decide +kernel

private theorem step_rank_value_b21 : ∀ i : Fin 48, 0 < rankValue (1008+i.val) → rankValue (nextValue (1008+i.val)) + 1 = rankValue (1008+i.val) := by decide +kernel

private theorem step_rank_value_b22 : ∀ i : Fin 48, 0 < rankValue (1056+i.val) → rankValue (nextValue (1056+i.val)) + 1 = rankValue (1056+i.val) := by decide +kernel

private theorem step_rank_value_b23 : ∀ i : Fin 48, 0 < rankValue (1104+i.val) → rankValue (nextValue (1104+i.val)) + 1 = rankValue (1104+i.val) := by decide +kernel

private theorem step_rank_value_b24 : ∀ i : Fin 48, 0 < rankValue (1152+i.val) → rankValue (nextValue (1152+i.val)) + 1 = rankValue (1152+i.val) := by decide +kernel

private theorem step_rank_value_b25 : ∀ i : Fin 48, 0 < rankValue (1200+i.val) → rankValue (nextValue (1200+i.val)) + 1 = rankValue (1200+i.val) := by decide +kernel

private theorem step_rank_value_b26 : ∀ i : Fin 48, 0 < rankValue (1248+i.val) → rankValue (nextValue (1248+i.val)) + 1 = rankValue (1248+i.val) := by decide +kernel

private theorem step_rank_value_b27 : ∀ i : Fin 48, 0 < rankValue (1296+i.val) → rankValue (nextValue (1296+i.val)) + 1 = rankValue (1296+i.val) := by decide +kernel

private theorem step_rank_value_b28 : ∀ i : Fin 48, 0 < rankValue (1344+i.val) → rankValue (nextValue (1344+i.val)) + 1 = rankValue (1344+i.val) := by decide +kernel

private theorem step_rank_value_b29 : ∀ i : Fin 48, 0 < rankValue (1392+i.val) → rankValue (nextValue (1392+i.val)) + 1 = rankValue (1392+i.val) := by decide +kernel

private theorem step_rank_value_b30 : ∀ i : Fin 48, 0 < rankValue (1440+i.val) → rankValue (nextValue (1440+i.val)) + 1 = rankValue (1440+i.val) := by decide +kernel

private theorem step_rank_value_b31 : ∀ i : Fin 48, 0 < rankValue (1488+i.val) → rankValue (nextValue (1488+i.val)) + 1 = rankValue (1488+i.val) := by decide +kernel

private theorem step_rank_value_b32 : ∀ i : Fin 48, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) := by decide +kernel

private theorem step_rank_value_b33 : ∀ i : Fin 48, 0 < rankValue (1584+i.val) → rankValue (nextValue (1584+i.val)) + 1 = rankValue (1584+i.val) := by decide +kernel

private theorem step_rank_value_b34 : ∀ i : Fin 48, 0 < rankValue (1632+i.val) → rankValue (nextValue (1632+i.val)) + 1 = rankValue (1632+i.val) := by decide +kernel

private theorem step_rank_value_b35 : ∀ i : Fin 48, 0 < rankValue (1680+i.val) → rankValue (nextValue (1680+i.val)) + 1 = rankValue (1680+i.val) := by decide +kernel

private theorem step_rank_value_b36 : ∀ i : Fin 48, 0 < rankValue (1728+i.val) → rankValue (nextValue (1728+i.val)) + 1 = rankValue (1728+i.val) := by decide +kernel

private theorem step_rank_value_b37 : ∀ i : Fin 48, 0 < rankValue (1776+i.val) → rankValue (nextValue (1776+i.val)) + 1 = rankValue (1776+i.val) := by decide +kernel

private theorem step_rank_value_b38 : ∀ i : Fin 48, 0 < rankValue (1824+i.val) → rankValue (nextValue (1824+i.val)) + 1 = rankValue (1824+i.val) := by decide +kernel

private theorem step_rank_value_b39 : ∀ i : Fin 48, 0 < rankValue (1872+i.val) → rankValue (nextValue (1872+i.val)) + 1 = rankValue (1872+i.val) := by decide +kernel

private theorem step_rank_value_b40 : ∀ i : Fin 48, 0 < rankValue (1920+i.val) → rankValue (nextValue (1920+i.val)) + 1 = rankValue (1920+i.val) := by decide +kernel

private theorem step_rank_value_b41 : ∀ i : Fin 48, 0 < rankValue (1968+i.val) → rankValue (nextValue (1968+i.val)) + 1 = rankValue (1968+i.val) := by decide +kernel

private theorem step_rank_value_b42 : ∀ i : Fin 48, 0 < rankValue (2016+i.val) → rankValue (nextValue (2016+i.val)) + 1 = rankValue (2016+i.val) := by decide +kernel

private theorem step_rank_value_b43 : ∀ i : Fin 48, 0 < rankValue (2064+i.val) → rankValue (nextValue (2064+i.val)) + 1 = rankValue (2064+i.val) := by decide +kernel

private theorem step_rank_value_b44 : ∀ i : Fin 48, 0 < rankValue (2112+i.val) → rankValue (nextValue (2112+i.val)) + 1 = rankValue (2112+i.val) := by decide +kernel

private theorem step_rank_value_b45 : ∀ i : Fin 48, 0 < rankValue (2160+i.val) → rankValue (nextValue (2160+i.val)) + 1 = rankValue (2160+i.val) := by decide +kernel

private theorem step_rank_value_b46 : ∀ i : Fin 48, 0 < rankValue (2208+i.val) → rankValue (nextValue (2208+i.val)) + 1 = rankValue (2208+i.val) := by decide +kernel

private theorem step_rank_value_b47 : ∀ i : Fin 48, 0 < rankValue (2256+i.val) → rankValue (nextValue (2256+i.val)) + 1 = rankValue (2256+i.val) := by decide +kernel

private theorem step_rank_value_b48 : ∀ i : Fin 48, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) := by decide +kernel

private theorem step_rank_value_b49 : ∀ i : Fin 48, 0 < rankValue (2352+i.val) → rankValue (nextValue (2352+i.val)) + 1 = rankValue (2352+i.val) := by decide +kernel

private theorem step_rank_value_b50 : ∀ i : Fin 48, 0 < rankValue (2400+i.val) → rankValue (nextValue (2400+i.val)) + 1 = rankValue (2400+i.val) := by decide +kernel

private theorem step_rank_value_b51 : ∀ i : Fin 48, 0 < rankValue (2448+i.val) → rankValue (nextValue (2448+i.val)) + 1 = rankValue (2448+i.val) := by decide +kernel

private theorem step_rank_value_b52 : ∀ i : Fin 48, 0 < rankValue (2496+i.val) → rankValue (nextValue (2496+i.val)) + 1 = rankValue (2496+i.val) := by decide +kernel

private theorem step_rank_value_b53 : ∀ i : Fin 48, 0 < rankValue (2544+i.val) → rankValue (nextValue (2544+i.val)) + 1 = rankValue (2544+i.val) := by decide +kernel

private theorem step_rank_value_b54 : ∀ i : Fin 48, 0 < rankValue (2592+i.val) → rankValue (nextValue (2592+i.val)) + 1 = rankValue (2592+i.val) := by decide +kernel

private theorem step_rank_value_b55 : ∀ i : Fin 48, 0 < rankValue (2640+i.val) → rankValue (nextValue (2640+i.val)) + 1 = rankValue (2640+i.val) := by decide +kernel

private theorem step_rank_value_b56 : ∀ i : Fin 48, 0 < rankValue (2688+i.val) → rankValue (nextValue (2688+i.val)) + 1 = rankValue (2688+i.val) := by decide +kernel

private theorem step_rank_value_b57 : ∀ i : Fin 48, 0 < rankValue (2736+i.val) → rankValue (nextValue (2736+i.val)) + 1 = rankValue (2736+i.val) := by decide +kernel

private theorem step_rank_value_b58 : ∀ i : Fin 48, 0 < rankValue (2784+i.val) → rankValue (nextValue (2784+i.val)) + 1 = rankValue (2784+i.val) := by decide +kernel

private theorem step_rank_value_b59 : ∀ i : Fin 48, 0 < rankValue (2832+i.val) → rankValue (nextValue (2832+i.val)) + 1 = rankValue (2832+i.val) := by decide +kernel

private theorem step_rank_value_b60 : ∀ i : Fin 48, 0 < rankValue (2880+i.val) → rankValue (nextValue (2880+i.val)) + 1 = rankValue (2880+i.val) := by decide +kernel

private theorem step_rank_value_b61 : ∀ i : Fin 48, 0 < rankValue (2928+i.val) → rankValue (nextValue (2928+i.val)) + 1 = rankValue (2928+i.val) := by decide +kernel

private theorem step_rank_value_b62 : ∀ i : Fin 48, 0 < rankValue (2976+i.val) → rankValue (nextValue (2976+i.val)) + 1 = rankValue (2976+i.val) := by decide +kernel

private theorem step_rank_value_b63 : ∀ i : Fin 48, 0 < rankValue (3024+i.val) → rankValue (nextValue (3024+i.val)) + 1 = rankValue (3024+i.val) := by decide +kernel

private theorem step_rank_value_b64 : ∀ i : Fin 48, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) := by decide +kernel

private theorem step_rank_value_b65 : ∀ i : Fin 48, 0 < rankValue (3120+i.val) → rankValue (nextValue (3120+i.val)) + 1 = rankValue (3120+i.val) := by decide +kernel

private theorem step_rank_value_b66 : ∀ i : Fin 48, 0 < rankValue (3168+i.val) → rankValue (nextValue (3168+i.val)) + 1 = rankValue (3168+i.val) := by decide +kernel

private theorem step_rank_value_b67 : ∀ i : Fin 48, 0 < rankValue (3216+i.val) → rankValue (nextValue (3216+i.val)) + 1 = rankValue (3216+i.val) := by decide +kernel

private theorem step_rank_value_b68 : ∀ i : Fin 48, 0 < rankValue (3264+i.val) → rankValue (nextValue (3264+i.val)) + 1 = rankValue (3264+i.val) := by decide +kernel

private theorem step_rank_value_b69 : ∀ i : Fin 48, 0 < rankValue (3312+i.val) → rankValue (nextValue (3312+i.val)) + 1 = rankValue (3312+i.val) := by decide +kernel

private theorem step_rank_value_b70 : ∀ i : Fin 48, 0 < rankValue (3360+i.val) → rankValue (nextValue (3360+i.val)) + 1 = rankValue (3360+i.val) := by decide +kernel

private theorem step_rank_value_b71 : ∀ i : Fin 48, 0 < rankValue (3408+i.val) → rankValue (nextValue (3408+i.val)) + 1 = rankValue (3408+i.val) := by decide +kernel

private theorem step_rank_value_b72 : ∀ i : Fin 48, 0 < rankValue (3456+i.val) → rankValue (nextValue (3456+i.val)) + 1 = rankValue (3456+i.val) := by decide +kernel

private theorem step_rank_value_b73 : ∀ i : Fin 48, 0 < rankValue (3504+i.val) → rankValue (nextValue (3504+i.val)) + 1 = rankValue (3504+i.val) := by decide +kernel

private theorem step_rank_value_b74 : ∀ i : Fin 48, 0 < rankValue (3552+i.val) → rankValue (nextValue (3552+i.val)) + 1 = rankValue (3552+i.val) := by decide +kernel

private theorem step_rank_value_b75 : ∀ i : Fin 48, 0 < rankValue (3600+i.val) → rankValue (nextValue (3600+i.val)) + 1 = rankValue (3600+i.val) := by decide +kernel

private theorem step_rank_value_b76 : ∀ i : Fin 48, 0 < rankValue (3648+i.val) → rankValue (nextValue (3648+i.val)) + 1 = rankValue (3648+i.val) := by decide +kernel

private theorem step_rank_value_b77 : ∀ i : Fin 48, 0 < rankValue (3696+i.val) → rankValue (nextValue (3696+i.val)) + 1 = rankValue (3696+i.val) := by decide +kernel

private theorem step_rank_value_b78 : ∀ i : Fin 48, 0 < rankValue (3744+i.val) → rankValue (nextValue (3744+i.val)) + 1 = rankValue (3744+i.val) := by decide +kernel

private theorem step_rank_value_b79 : ∀ i : Fin 48, 0 < rankValue (3792+i.val) → rankValue (nextValue (3792+i.val)) + 1 = rankValue (3792+i.val) := by decide +kernel

private theorem step_rank_value_b80 : ∀ i : Fin 48, 0 < rankValue (3840+i.val) → rankValue (nextValue (3840+i.val)) + 1 = rankValue (3840+i.val) := by decide +kernel

private theorem step_rank_value_b81 : ∀ i : Fin 48, 0 < rankValue (3888+i.val) → rankValue (nextValue (3888+i.val)) + 1 = rankValue (3888+i.val) := by decide +kernel

private theorem step_rank_value_b82 : ∀ i : Fin 48, 0 < rankValue (3936+i.val) → rankValue (nextValue (3936+i.val)) + 1 = rankValue (3936+i.val) := by decide +kernel

private theorem step_rank_value_b83 : ∀ i : Fin 48, 0 < rankValue (3984+i.val) → rankValue (nextValue (3984+i.val)) + 1 = rankValue (3984+i.val) := by decide +kernel

private theorem step_rank_value_b84 : ∀ i : Fin 48, 0 < rankValue (4032+i.val) → rankValue (nextValue (4032+i.val)) + 1 = rankValue (4032+i.val) := by decide +kernel

private theorem step_rank_value_b85 : ∀ i : Fin 48, 0 < rankValue (4080+i.val) → rankValue (nextValue (4080+i.val)) + 1 = rankValue (4080+i.val) := by decide +kernel

private theorem step_rank_value_b86 : ∀ i : Fin 48, 0 < rankValue (4128+i.val) → rankValue (nextValue (4128+i.val)) + 1 = rankValue (4128+i.val) := by decide +kernel

private theorem step_rank_value_b87 : ∀ i : Fin 48, 0 < rankValue (4176+i.val) → rankValue (nextValue (4176+i.val)) + 1 = rankValue (4176+i.val) := by decide +kernel

private theorem step_rank_value_b88 : ∀ i : Fin 48, 0 < rankValue (4224+i.val) → rankValue (nextValue (4224+i.val)) + 1 = rankValue (4224+i.val) := by decide +kernel

private theorem step_rank_value_b89 : ∀ i : Fin 48, 0 < rankValue (4272+i.val) → rankValue (nextValue (4272+i.val)) + 1 = rankValue (4272+i.val) := by decide +kernel

private theorem step_rank_value_b90 : ∀ i : Fin 48, 0 < rankValue (4320+i.val) → rankValue (nextValue (4320+i.val)) + 1 = rankValue (4320+i.val) := by decide +kernel

private theorem step_rank_value_b91 : ∀ i : Fin 48, 0 < rankValue (4368+i.val) → rankValue (nextValue (4368+i.val)) + 1 = rankValue (4368+i.val) := by decide +kernel

private theorem step_rank_value_b92 : ∀ i : Fin 48, 0 < rankValue (4416+i.val) → rankValue (nextValue (4416+i.val)) + 1 = rankValue (4416+i.val) := by decide +kernel

private theorem step_rank_value_b93 : ∀ i : Fin 48, 0 < rankValue (4464+i.val) → rankValue (nextValue (4464+i.val)) + 1 = rankValue (4464+i.val) := by decide +kernel

private theorem step_rank_value_b94 : ∀ i : Fin 48, 0 < rankValue (4512+i.val) → rankValue (nextValue (4512+i.val)) + 1 = rankValue (4512+i.val) := by decide +kernel

private theorem step_rank_value_b95 : ∀ i : Fin 48, 0 < rankValue (4560+i.val) → rankValue (nextValue (4560+i.val)) + 1 = rankValue (4560+i.val) := by decide +kernel

private theorem step_rank_value_b96 : ∀ i : Fin 48, 0 < rankValue (4608+i.val) → rankValue (nextValue (4608+i.val)) + 1 = rankValue (4608+i.val) := by decide +kernel

private theorem step_rank_value_b97 : ∀ i : Fin 48, 0 < rankValue (4656+i.val) → rankValue (nextValue (4656+i.val)) + 1 = rankValue (4656+i.val) := by decide +kernel

private theorem step_rank_value_b98 : ∀ i : Fin 48, 0 < rankValue (4704+i.val) → rankValue (nextValue (4704+i.val)) + 1 = rankValue (4704+i.val) := by decide +kernel

private theorem step_rank_value_b99 : ∀ i : Fin 48, 0 < rankValue (4752+i.val) → rankValue (nextValue (4752+i.val)) + 1 = rankValue (4752+i.val) := by decide +kernel

private theorem step_rank_value_b100 : ∀ i : Fin 48, 0 < rankValue (4800+i.val) → rankValue (nextValue (4800+i.val)) + 1 = rankValue (4800+i.val) := by decide +kernel

private theorem step_rank_value_b101 : ∀ i : Fin 48, 0 < rankValue (4848+i.val) → rankValue (nextValue (4848+i.val)) + 1 = rankValue (4848+i.val) := by decide +kernel

private theorem step_rank_value_b102 : ∀ i : Fin 48, 0 < rankValue (4896+i.val) → rankValue (nextValue (4896+i.val)) + 1 = rankValue (4896+i.val) := by decide +kernel

private theorem step_rank_value_b103 : ∀ i : Fin 48, 0 < rankValue (4944+i.val) → rankValue (nextValue (4944+i.val)) + 1 = rankValue (4944+i.val) := by decide +kernel

private theorem step_rank_value_b104 : ∀ i : Fin 48, 0 < rankValue (4992+i.val) → rankValue (nextValue (4992+i.val)) + 1 = rankValue (4992+i.val) := by decide +kernel

private theorem step_rank_value_b105 : ∀ i : Fin 48, 0 < rankValue (5040+i.val) → rankValue (nextValue (5040+i.val)) + 1 = rankValue (5040+i.val) := by decide +kernel

private theorem step_rank_value_b106 : ∀ i : Fin 48, 0 < rankValue (5088+i.val) → rankValue (nextValue (5088+i.val)) + 1 = rankValue (5088+i.val) := by decide +kernel

private theorem step_rank_value_b107 : ∀ i : Fin 48, 0 < rankValue (5136+i.val) → rankValue (nextValue (5136+i.val)) + 1 = rankValue (5136+i.val) := by decide +kernel

private theorem step_rank_value_b108 : ∀ i : Fin 48, 0 < rankValue (5184+i.val) → rankValue (nextValue (5184+i.val)) + 1 = rankValue (5184+i.val) := by decide +kernel

private theorem step_rank_value_b109 : ∀ i : Fin 32, 0 < rankValue (5232+i.val) → rankValue (nextValue (5232+i.val)) + 1 = rankValue (5232+i.val) := by decide +kernel

private theorem step_rank_value_n0_0 : ∀ i : Fin 96, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 48 48 step_rank_value_b0 step_rank_value_b1

private theorem step_rank_value_n0_1 : ∀ i : Fin 96, 0 < rankValue (96+i.val) → rankValue (nextValue (96+i.val)) + 1 = rankValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 96 48 48 step_rank_value_b2 step_rank_value_b3

private theorem step_rank_value_n0_2 : ∀ i : Fin 96, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 192 48 48 step_rank_value_b4 step_rank_value_b5

private theorem step_rank_value_n0_3 : ∀ i : Fin 96, 0 < rankValue (288+i.val) → rankValue (nextValue (288+i.val)) + 1 = rankValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 288 48 48 step_rank_value_b6 step_rank_value_b7

private theorem step_rank_value_n0_4 : ∀ i : Fin 96, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 384 48 48 step_rank_value_b8 step_rank_value_b9

private theorem step_rank_value_n0_5 : ∀ i : Fin 96, 0 < rankValue (480+i.val) → rankValue (nextValue (480+i.val)) + 1 = rankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 480 48 48 step_rank_value_b10 step_rank_value_b11

private theorem step_rank_value_n0_6 : ∀ i : Fin 96, 0 < rankValue (576+i.val) → rankValue (nextValue (576+i.val)) + 1 = rankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 576 48 48 step_rank_value_b12 step_rank_value_b13

private theorem step_rank_value_n0_7 : ∀ i : Fin 96, 0 < rankValue (672+i.val) → rankValue (nextValue (672+i.val)) + 1 = rankValue (672+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 672 48 48 step_rank_value_b14 step_rank_value_b15

private theorem step_rank_value_n0_8 : ∀ i : Fin 96, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 768 48 48 step_rank_value_b16 step_rank_value_b17

private theorem step_rank_value_n0_9 : ∀ i : Fin 96, 0 < rankValue (864+i.val) → rankValue (nextValue (864+i.val)) + 1 = rankValue (864+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 864 48 48 step_rank_value_b18 step_rank_value_b19

private theorem step_rank_value_n0_10 : ∀ i : Fin 96, 0 < rankValue (960+i.val) → rankValue (nextValue (960+i.val)) + 1 = rankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 960 48 48 step_rank_value_b20 step_rank_value_b21

private theorem step_rank_value_n0_11 : ∀ i : Fin 96, 0 < rankValue (1056+i.val) → rankValue (nextValue (1056+i.val)) + 1 = rankValue (1056+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1056 48 48 step_rank_value_b22 step_rank_value_b23

private theorem step_rank_value_n0_12 : ∀ i : Fin 96, 0 < rankValue (1152+i.val) → rankValue (nextValue (1152+i.val)) + 1 = rankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1152 48 48 step_rank_value_b24 step_rank_value_b25

private theorem step_rank_value_n0_13 : ∀ i : Fin 96, 0 < rankValue (1248+i.val) → rankValue (nextValue (1248+i.val)) + 1 = rankValue (1248+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1248 48 48 step_rank_value_b26 step_rank_value_b27

private theorem step_rank_value_n0_14 : ∀ i : Fin 96, 0 < rankValue (1344+i.val) → rankValue (nextValue (1344+i.val)) + 1 = rankValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1344 48 48 step_rank_value_b28 step_rank_value_b29

private theorem step_rank_value_n0_15 : ∀ i : Fin 96, 0 < rankValue (1440+i.val) → rankValue (nextValue (1440+i.val)) + 1 = rankValue (1440+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1440 48 48 step_rank_value_b30 step_rank_value_b31

private theorem step_rank_value_n0_16 : ∀ i : Fin 96, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 48 48 step_rank_value_b32 step_rank_value_b33

private theorem step_rank_value_n0_17 : ∀ i : Fin 96, 0 < rankValue (1632+i.val) → rankValue (nextValue (1632+i.val)) + 1 = rankValue (1632+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1632 48 48 step_rank_value_b34 step_rank_value_b35

private theorem step_rank_value_n0_18 : ∀ i : Fin 96, 0 < rankValue (1728+i.val) → rankValue (nextValue (1728+i.val)) + 1 = rankValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1728 48 48 step_rank_value_b36 step_rank_value_b37

private theorem step_rank_value_n0_19 : ∀ i : Fin 96, 0 < rankValue (1824+i.val) → rankValue (nextValue (1824+i.val)) + 1 = rankValue (1824+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1824 48 48 step_rank_value_b38 step_rank_value_b39

private theorem step_rank_value_n0_20 : ∀ i : Fin 96, 0 < rankValue (1920+i.val) → rankValue (nextValue (1920+i.val)) + 1 = rankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1920 48 48 step_rank_value_b40 step_rank_value_b41

private theorem step_rank_value_n0_21 : ∀ i : Fin 96, 0 < rankValue (2016+i.val) → rankValue (nextValue (2016+i.val)) + 1 = rankValue (2016+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2016 48 48 step_rank_value_b42 step_rank_value_b43

private theorem step_rank_value_n0_22 : ∀ i : Fin 96, 0 < rankValue (2112+i.val) → rankValue (nextValue (2112+i.val)) + 1 = rankValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2112 48 48 step_rank_value_b44 step_rank_value_b45

private theorem step_rank_value_n0_23 : ∀ i : Fin 96, 0 < rankValue (2208+i.val) → rankValue (nextValue (2208+i.val)) + 1 = rankValue (2208+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2208 48 48 step_rank_value_b46 step_rank_value_b47

private theorem step_rank_value_n0_24 : ∀ i : Fin 96, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2304 48 48 step_rank_value_b48 step_rank_value_b49

private theorem step_rank_value_n0_25 : ∀ i : Fin 96, 0 < rankValue (2400+i.val) → rankValue (nextValue (2400+i.val)) + 1 = rankValue (2400+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2400 48 48 step_rank_value_b50 step_rank_value_b51

private theorem step_rank_value_n0_26 : ∀ i : Fin 96, 0 < rankValue (2496+i.val) → rankValue (nextValue (2496+i.val)) + 1 = rankValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2496 48 48 step_rank_value_b52 step_rank_value_b53

private theorem step_rank_value_n0_27 : ∀ i : Fin 96, 0 < rankValue (2592+i.val) → rankValue (nextValue (2592+i.val)) + 1 = rankValue (2592+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2592 48 48 step_rank_value_b54 step_rank_value_b55

private theorem step_rank_value_n0_28 : ∀ i : Fin 96, 0 < rankValue (2688+i.val) → rankValue (nextValue (2688+i.val)) + 1 = rankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2688 48 48 step_rank_value_b56 step_rank_value_b57

private theorem step_rank_value_n0_29 : ∀ i : Fin 96, 0 < rankValue (2784+i.val) → rankValue (nextValue (2784+i.val)) + 1 = rankValue (2784+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2784 48 48 step_rank_value_b58 step_rank_value_b59

private theorem step_rank_value_n0_30 : ∀ i : Fin 96, 0 < rankValue (2880+i.val) → rankValue (nextValue (2880+i.val)) + 1 = rankValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2880 48 48 step_rank_value_b60 step_rank_value_b61

private theorem step_rank_value_n0_31 : ∀ i : Fin 96, 0 < rankValue (2976+i.val) → rankValue (nextValue (2976+i.val)) + 1 = rankValue (2976+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2976 48 48 step_rank_value_b62 step_rank_value_b63

private theorem step_rank_value_n0_32 : ∀ i : Fin 96, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 48 48 step_rank_value_b64 step_rank_value_b65

private theorem step_rank_value_n0_33 : ∀ i : Fin 96, 0 < rankValue (3168+i.val) → rankValue (nextValue (3168+i.val)) + 1 = rankValue (3168+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3168 48 48 step_rank_value_b66 step_rank_value_b67

private theorem step_rank_value_n0_34 : ∀ i : Fin 96, 0 < rankValue (3264+i.val) → rankValue (nextValue (3264+i.val)) + 1 = rankValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3264 48 48 step_rank_value_b68 step_rank_value_b69

private theorem step_rank_value_n0_35 : ∀ i : Fin 96, 0 < rankValue (3360+i.val) → rankValue (nextValue (3360+i.val)) + 1 = rankValue (3360+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3360 48 48 step_rank_value_b70 step_rank_value_b71

private theorem step_rank_value_n0_36 : ∀ i : Fin 96, 0 < rankValue (3456+i.val) → rankValue (nextValue (3456+i.val)) + 1 = rankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3456 48 48 step_rank_value_b72 step_rank_value_b73

private theorem step_rank_value_n0_37 : ∀ i : Fin 96, 0 < rankValue (3552+i.val) → rankValue (nextValue (3552+i.val)) + 1 = rankValue (3552+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3552 48 48 step_rank_value_b74 step_rank_value_b75

private theorem step_rank_value_n0_38 : ∀ i : Fin 96, 0 < rankValue (3648+i.val) → rankValue (nextValue (3648+i.val)) + 1 = rankValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3648 48 48 step_rank_value_b76 step_rank_value_b77

private theorem step_rank_value_n0_39 : ∀ i : Fin 96, 0 < rankValue (3744+i.val) → rankValue (nextValue (3744+i.val)) + 1 = rankValue (3744+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3744 48 48 step_rank_value_b78 step_rank_value_b79

private theorem step_rank_value_n0_40 : ∀ i : Fin 96, 0 < rankValue (3840+i.val) → rankValue (nextValue (3840+i.val)) + 1 = rankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3840 48 48 step_rank_value_b80 step_rank_value_b81

private theorem step_rank_value_n0_41 : ∀ i : Fin 96, 0 < rankValue (3936+i.val) → rankValue (nextValue (3936+i.val)) + 1 = rankValue (3936+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3936 48 48 step_rank_value_b82 step_rank_value_b83

private theorem step_rank_value_n0_42 : ∀ i : Fin 96, 0 < rankValue (4032+i.val) → rankValue (nextValue (4032+i.val)) + 1 = rankValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4032 48 48 step_rank_value_b84 step_rank_value_b85

private theorem step_rank_value_n0_43 : ∀ i : Fin 96, 0 < rankValue (4128+i.val) → rankValue (nextValue (4128+i.val)) + 1 = rankValue (4128+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4128 48 48 step_rank_value_b86 step_rank_value_b87

private theorem step_rank_value_n0_44 : ∀ i : Fin 96, 0 < rankValue (4224+i.val) → rankValue (nextValue (4224+i.val)) + 1 = rankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4224 48 48 step_rank_value_b88 step_rank_value_b89

private theorem step_rank_value_n0_45 : ∀ i : Fin 96, 0 < rankValue (4320+i.val) → rankValue (nextValue (4320+i.val)) + 1 = rankValue (4320+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4320 48 48 step_rank_value_b90 step_rank_value_b91

private theorem step_rank_value_n0_46 : ∀ i : Fin 96, 0 < rankValue (4416+i.val) → rankValue (nextValue (4416+i.val)) + 1 = rankValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4416 48 48 step_rank_value_b92 step_rank_value_b93

private theorem step_rank_value_n0_47 : ∀ i : Fin 96, 0 < rankValue (4512+i.val) → rankValue (nextValue (4512+i.val)) + 1 = rankValue (4512+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4512 48 48 step_rank_value_b94 step_rank_value_b95

private theorem step_rank_value_n0_48 : ∀ i : Fin 96, 0 < rankValue (4608+i.val) → rankValue (nextValue (4608+i.val)) + 1 = rankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4608 48 48 step_rank_value_b96 step_rank_value_b97

private theorem step_rank_value_n0_49 : ∀ i : Fin 96, 0 < rankValue (4704+i.val) → rankValue (nextValue (4704+i.val)) + 1 = rankValue (4704+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4704 48 48 step_rank_value_b98 step_rank_value_b99

private theorem step_rank_value_n0_50 : ∀ i : Fin 96, 0 < rankValue (4800+i.val) → rankValue (nextValue (4800+i.val)) + 1 = rankValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4800 48 48 step_rank_value_b100 step_rank_value_b101

private theorem step_rank_value_n0_51 : ∀ i : Fin 96, 0 < rankValue (4896+i.val) → rankValue (nextValue (4896+i.val)) + 1 = rankValue (4896+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4896 48 48 step_rank_value_b102 step_rank_value_b103

private theorem step_rank_value_n0_52 : ∀ i : Fin 96, 0 < rankValue (4992+i.val) → rankValue (nextValue (4992+i.val)) + 1 = rankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4992 48 48 step_rank_value_b104 step_rank_value_b105

private theorem step_rank_value_n0_53 : ∀ i : Fin 96, 0 < rankValue (5088+i.val) → rankValue (nextValue (5088+i.val)) + 1 = rankValue (5088+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 5088 48 48 step_rank_value_b106 step_rank_value_b107

private theorem step_rank_value_n0_54 : ∀ i : Fin 80, 0 < rankValue (5184+i.val) → rankValue (nextValue (5184+i.val)) + 1 = rankValue (5184+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 5184 48 32 step_rank_value_b108 step_rank_value_b109

private theorem step_rank_value_n1_0 : ∀ i : Fin 192, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 96 96 step_rank_value_n0_0 step_rank_value_n0_1

private theorem step_rank_value_n1_1 : ∀ i : Fin 192, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 192 96 96 step_rank_value_n0_2 step_rank_value_n0_3

private theorem step_rank_value_n1_2 : ∀ i : Fin 192, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 384 96 96 step_rank_value_n0_4 step_rank_value_n0_5

private theorem step_rank_value_n1_3 : ∀ i : Fin 192, 0 < rankValue (576+i.val) → rankValue (nextValue (576+i.val)) + 1 = rankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 576 96 96 step_rank_value_n0_6 step_rank_value_n0_7

private theorem step_rank_value_n1_4 : ∀ i : Fin 192, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 768 96 96 step_rank_value_n0_8 step_rank_value_n0_9

private theorem step_rank_value_n1_5 : ∀ i : Fin 192, 0 < rankValue (960+i.val) → rankValue (nextValue (960+i.val)) + 1 = rankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 960 96 96 step_rank_value_n0_10 step_rank_value_n0_11

private theorem step_rank_value_n1_6 : ∀ i : Fin 192, 0 < rankValue (1152+i.val) → rankValue (nextValue (1152+i.val)) + 1 = rankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1152 96 96 step_rank_value_n0_12 step_rank_value_n0_13

private theorem step_rank_value_n1_7 : ∀ i : Fin 192, 0 < rankValue (1344+i.val) → rankValue (nextValue (1344+i.val)) + 1 = rankValue (1344+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1344 96 96 step_rank_value_n0_14 step_rank_value_n0_15

private theorem step_rank_value_n1_8 : ∀ i : Fin 192, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 96 96 step_rank_value_n0_16 step_rank_value_n0_17

private theorem step_rank_value_n1_9 : ∀ i : Fin 192, 0 < rankValue (1728+i.val) → rankValue (nextValue (1728+i.val)) + 1 = rankValue (1728+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1728 96 96 step_rank_value_n0_18 step_rank_value_n0_19

private theorem step_rank_value_n1_10 : ∀ i : Fin 192, 0 < rankValue (1920+i.val) → rankValue (nextValue (1920+i.val)) + 1 = rankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1920 96 96 step_rank_value_n0_20 step_rank_value_n0_21

private theorem step_rank_value_n1_11 : ∀ i : Fin 192, 0 < rankValue (2112+i.val) → rankValue (nextValue (2112+i.val)) + 1 = rankValue (2112+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2112 96 96 step_rank_value_n0_22 step_rank_value_n0_23

private theorem step_rank_value_n1_12 : ∀ i : Fin 192, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2304 96 96 step_rank_value_n0_24 step_rank_value_n0_25

private theorem step_rank_value_n1_13 : ∀ i : Fin 192, 0 < rankValue (2496+i.val) → rankValue (nextValue (2496+i.val)) + 1 = rankValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2496 96 96 step_rank_value_n0_26 step_rank_value_n0_27

private theorem step_rank_value_n1_14 : ∀ i : Fin 192, 0 < rankValue (2688+i.val) → rankValue (nextValue (2688+i.val)) + 1 = rankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2688 96 96 step_rank_value_n0_28 step_rank_value_n0_29

private theorem step_rank_value_n1_15 : ∀ i : Fin 192, 0 < rankValue (2880+i.val) → rankValue (nextValue (2880+i.val)) + 1 = rankValue (2880+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2880 96 96 step_rank_value_n0_30 step_rank_value_n0_31

private theorem step_rank_value_n1_16 : ∀ i : Fin 192, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 96 96 step_rank_value_n0_32 step_rank_value_n0_33

private theorem step_rank_value_n1_17 : ∀ i : Fin 192, 0 < rankValue (3264+i.val) → rankValue (nextValue (3264+i.val)) + 1 = rankValue (3264+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3264 96 96 step_rank_value_n0_34 step_rank_value_n0_35

private theorem step_rank_value_n1_18 : ∀ i : Fin 192, 0 < rankValue (3456+i.val) → rankValue (nextValue (3456+i.val)) + 1 = rankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3456 96 96 step_rank_value_n0_36 step_rank_value_n0_37

private theorem step_rank_value_n1_19 : ∀ i : Fin 192, 0 < rankValue (3648+i.val) → rankValue (nextValue (3648+i.val)) + 1 = rankValue (3648+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3648 96 96 step_rank_value_n0_38 step_rank_value_n0_39

private theorem step_rank_value_n1_20 : ∀ i : Fin 192, 0 < rankValue (3840+i.val) → rankValue (nextValue (3840+i.val)) + 1 = rankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3840 96 96 step_rank_value_n0_40 step_rank_value_n0_41

private theorem step_rank_value_n1_21 : ∀ i : Fin 192, 0 < rankValue (4032+i.val) → rankValue (nextValue (4032+i.val)) + 1 = rankValue (4032+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4032 96 96 step_rank_value_n0_42 step_rank_value_n0_43

private theorem step_rank_value_n1_22 : ∀ i : Fin 192, 0 < rankValue (4224+i.val) → rankValue (nextValue (4224+i.val)) + 1 = rankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4224 96 96 step_rank_value_n0_44 step_rank_value_n0_45

private theorem step_rank_value_n1_23 : ∀ i : Fin 192, 0 < rankValue (4416+i.val) → rankValue (nextValue (4416+i.val)) + 1 = rankValue (4416+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4416 96 96 step_rank_value_n0_46 step_rank_value_n0_47

private theorem step_rank_value_n1_24 : ∀ i : Fin 192, 0 < rankValue (4608+i.val) → rankValue (nextValue (4608+i.val)) + 1 = rankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4608 96 96 step_rank_value_n0_48 step_rank_value_n0_49

private theorem step_rank_value_n1_25 : ∀ i : Fin 192, 0 < rankValue (4800+i.val) → rankValue (nextValue (4800+i.val)) + 1 = rankValue (4800+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4800 96 96 step_rank_value_n0_50 step_rank_value_n0_51

private theorem step_rank_value_n1_26 : ∀ i : Fin 192, 0 < rankValue (4992+i.val) → rankValue (nextValue (4992+i.val)) + 1 = rankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4992 96 96 step_rank_value_n0_52 step_rank_value_n0_53

private theorem step_rank_value_n2_0 : ∀ i : Fin 384, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 192 192 step_rank_value_n1_0 step_rank_value_n1_1

private theorem step_rank_value_n2_1 : ∀ i : Fin 384, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 384 192 192 step_rank_value_n1_2 step_rank_value_n1_3

private theorem step_rank_value_n2_2 : ∀ i : Fin 384, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 768 192 192 step_rank_value_n1_4 step_rank_value_n1_5

private theorem step_rank_value_n2_3 : ∀ i : Fin 384, 0 < rankValue (1152+i.val) → rankValue (nextValue (1152+i.val)) + 1 = rankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1152 192 192 step_rank_value_n1_6 step_rank_value_n1_7

private theorem step_rank_value_n2_4 : ∀ i : Fin 384, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 192 192 step_rank_value_n1_8 step_rank_value_n1_9

private theorem step_rank_value_n2_5 : ∀ i : Fin 384, 0 < rankValue (1920+i.val) → rankValue (nextValue (1920+i.val)) + 1 = rankValue (1920+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1920 192 192 step_rank_value_n1_10 step_rank_value_n1_11

private theorem step_rank_value_n2_6 : ∀ i : Fin 384, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2304 192 192 step_rank_value_n1_12 step_rank_value_n1_13

private theorem step_rank_value_n2_7 : ∀ i : Fin 384, 0 < rankValue (2688+i.val) → rankValue (nextValue (2688+i.val)) + 1 = rankValue (2688+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2688 192 192 step_rank_value_n1_14 step_rank_value_n1_15

private theorem step_rank_value_n2_8 : ∀ i : Fin 384, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 192 192 step_rank_value_n1_16 step_rank_value_n1_17

private theorem step_rank_value_n2_9 : ∀ i : Fin 384, 0 < rankValue (3456+i.val) → rankValue (nextValue (3456+i.val)) + 1 = rankValue (3456+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3456 192 192 step_rank_value_n1_18 step_rank_value_n1_19

private theorem step_rank_value_n2_10 : ∀ i : Fin 384, 0 < rankValue (3840+i.val) → rankValue (nextValue (3840+i.val)) + 1 = rankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3840 192 192 step_rank_value_n1_20 step_rank_value_n1_21

private theorem step_rank_value_n2_11 : ∀ i : Fin 384, 0 < rankValue (4224+i.val) → rankValue (nextValue (4224+i.val)) + 1 = rankValue (4224+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4224 192 192 step_rank_value_n1_22 step_rank_value_n1_23

private theorem step_rank_value_n2_12 : ∀ i : Fin 384, 0 < rankValue (4608+i.val) → rankValue (nextValue (4608+i.val)) + 1 = rankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4608 192 192 step_rank_value_n1_24 step_rank_value_n1_25

private theorem step_rank_value_n2_13 : ∀ i : Fin 272, 0 < rankValue (4992+i.val) → rankValue (nextValue (4992+i.val)) + 1 = rankValue (4992+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4992 192 80 step_rank_value_n1_26 step_rank_value_n0_54

private theorem step_rank_value_n3_0 : ∀ i : Fin 768, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 384 384 step_rank_value_n2_0 step_rank_value_n2_1

private theorem step_rank_value_n3_1 : ∀ i : Fin 768, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 768 384 384 step_rank_value_n2_2 step_rank_value_n2_3

private theorem step_rank_value_n3_2 : ∀ i : Fin 768, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 384 384 step_rank_value_n2_4 step_rank_value_n2_5

private theorem step_rank_value_n3_3 : ∀ i : Fin 768, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2304 384 384 step_rank_value_n2_6 step_rank_value_n2_7

private theorem step_rank_value_n3_4 : ∀ i : Fin 768, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 384 384 step_rank_value_n2_8 step_rank_value_n2_9

private theorem step_rank_value_n3_5 : ∀ i : Fin 768, 0 < rankValue (3840+i.val) → rankValue (nextValue (3840+i.val)) + 1 = rankValue (3840+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3840 384 384 step_rank_value_n2_10 step_rank_value_n2_11

private theorem step_rank_value_n3_6 : ∀ i : Fin 656, 0 < rankValue (4608+i.val) → rankValue (nextValue (4608+i.val)) + 1 = rankValue (4608+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 4608 384 272 step_rank_value_n2_12 step_rank_value_n2_13

private theorem step_rank_value_n4_0 : ∀ i : Fin 1536, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 768 768 step_rank_value_n3_0 step_rank_value_n3_1

private theorem step_rank_value_n4_1 : ∀ i : Fin 1536, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 768 768 step_rank_value_n3_2 step_rank_value_n3_3

private theorem step_rank_value_n4_2 : ∀ i : Fin 1536, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 768 768 step_rank_value_n3_4 step_rank_value_n3_5

private theorem step_rank_value_n5_0 : ∀ i : Fin 3072, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 1536 1536 step_rank_value_n4_0 step_rank_value_n4_1

private theorem step_rank_value_n5_1 : ∀ i : Fin 2192, 0 < rankValue (3072+i.val) → rankValue (nextValue (3072+i.val)) + 1 = rankValue (3072+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 3072 1536 656 step_rank_value_n4_2 step_rank_value_n3_6

private theorem step_rank_value_n6_0 : ∀ i : Fin 5264, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 3072 2192 step_rank_value_n5_0 step_rank_value_n5_1

theorem step_rank_value : ∀ i : Fin 5264, 0 < rankValue i.val → rankValue (nextValue i.val) + 1 = rankValue i.val := by
  simpa only [Nat.zero_add] using step_rank_value_n6_0

end PlanarHom.ColoringMacroFaces.FanFramed
