import PlanarHom.ColoringMacroWireFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
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

private theorem step_rank_value_b55 : ∀ i : Fin 6, 0 < rankValue (2640+i.val) → rankValue (nextValue (2640+i.val)) + 1 = rankValue (2640+i.val) := by decide +kernel

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

private theorem step_rank_value_n0_27 : ∀ i : Fin 54, 0 < rankValue (2592+i.val) → rankValue (nextValue (2592+i.val)) + 1 = rankValue (2592+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2592 48 6 step_rank_value_b54 step_rank_value_b55

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

private theorem step_rank_value_n1_13 : ∀ i : Fin 150, 0 < rankValue (2496+i.val) → rankValue (nextValue (2496+i.val)) + 1 = rankValue (2496+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2496 96 54 step_rank_value_n0_26 step_rank_value_n0_27

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

private theorem step_rank_value_n2_6 : ∀ i : Fin 342, 0 < rankValue (2304+i.val) → rankValue (nextValue (2304+i.val)) + 1 = rankValue (2304+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 2304 192 150 step_rank_value_n1_12 step_rank_value_n1_13

private theorem step_rank_value_n3_0 : ∀ i : Fin 768, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 384 384 step_rank_value_n2_0 step_rank_value_n2_1

private theorem step_rank_value_n3_1 : ∀ i : Fin 768, 0 < rankValue (768+i.val) → rankValue (nextValue (768+i.val)) + 1 = rankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 768 384 384 step_rank_value_n2_2 step_rank_value_n2_3

private theorem step_rank_value_n3_2 : ∀ i : Fin 768, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 384 384 step_rank_value_n2_4 step_rank_value_n2_5

private theorem step_rank_value_n4_0 : ∀ i : Fin 1536, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 768 768 step_rank_value_n3_0 step_rank_value_n3_1

private theorem step_rank_value_n4_1 : ∀ i : Fin 1110, 0 < rankValue (1536+i.val) → rankValue (nextValue (1536+i.val)) + 1 = rankValue (1536+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 1536 768 342 step_rank_value_n3_2 step_rank_value_n2_6

private theorem step_rank_value_n5_0 : ∀ i : Fin 2646, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 1536 1110 step_rank_value_n4_0 step_rank_value_n4_1

theorem step_rank_value : ∀ i : Fin 2646, 0 < rankValue i.val → rankValue (nextValue i.val) + 1 = rankValue i.val := by
  simpa only [Nat.zero_add] using step_rank_value_n5_0

end PlanarHom.ColoringMacroFaces.WireFramed
