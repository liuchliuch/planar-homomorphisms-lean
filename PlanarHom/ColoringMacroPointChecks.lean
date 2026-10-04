import PlanarHom.ColoringMacroPointCheckGroup72
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem pointBound_all (s : CellShape) (v : LocalPatch.NumericVertex s) : PointBound s v := by
  cases s
  case wireTop =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireTop_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireTop_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireTop_PointBound_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireTop_PointBound_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireTop_PointBound_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireTop_PointBound_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireTop_PointBound_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireTop_PointBound_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireTop_PointBound_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireBottom =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireBottom_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireBottom_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireBottom_PointBound_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireBottom_PointBound_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireBottom_PointBound_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireBottom_PointBound_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireBottom_PointBound_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireBottom_PointBound_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireBottom_PointBound_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireDown =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireDown_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireDown_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireDown_PointBound_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireDown_PointBound_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireDown_PointBound_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireDown_PointBound_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireDown_PointBound_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireDown_PointBound_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireDown_PointBound_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case cross =>
    have hv : v.val<1270 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_cross_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_cross_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_cross_PointBound_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_cross_PointBound_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_cross_PointBound_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_cross_PointBound_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_cross_PointBound_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_cross_PointBound_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_cross_PointBound_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_cross_PointBound_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_cross_PointBound_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_cross_PointBound_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_cross_PointBound_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_cross_PointBound_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_cross_PointBound_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_cross_PointBound_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_cross_PointBound_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_cross_PointBound_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_cross_PointBound_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1270
    · have h := check_cross_PointBound_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case fan =>
    have hv : v.val<1054 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_fan_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_fan_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_fan_PointBound_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_fan_PointBound_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_fan_PointBound_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_fan_PointBound_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_fan_PointBound_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_fan_PointBound_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_fan_PointBound_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_fan_PointBound_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_fan_PointBound_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_fan_PointBound_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_fan_PointBound_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_fan_PointBound_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_fan_PointBound_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_fan_PointBound_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1054
    · have h := check_fan_PointBound_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case test =>
    have hv : v.val<114 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_test_PointBound_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<114
    · have h := check_test_PointBound_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
theorem interiorOrPort_all (s : CellShape) (v : LocalPatch.NumericVertex s) : InteriorOrPort s v := by
  cases s
  case wireTop =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireTop_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireTop_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireTop_InteriorOrPort_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireTop_InteriorOrPort_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireTop_InteriorOrPort_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireTop_InteriorOrPort_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireTop_InteriorOrPort_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireTop_InteriorOrPort_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireTop_InteriorOrPort_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireBottom =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireBottom_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireBottom_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireBottom_InteriorOrPort_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireBottom_InteriorOrPort_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireBottom_InteriorOrPort_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireBottom_InteriorOrPort_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireBottom_InteriorOrPort_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireBottom_InteriorOrPort_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireBottom_InteriorOrPort_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireDown =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireDown_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireDown_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireDown_InteriorOrPort_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireDown_InteriorOrPort_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireDown_InteriorOrPort_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireDown_InteriorOrPort_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireDown_InteriorOrPort_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireDown_InteriorOrPort_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h := check_wireDown_InteriorOrPort_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case cross =>
    have hv : v.val<1270 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_cross_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_cross_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_cross_InteriorOrPort_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_cross_InteriorOrPort_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_cross_InteriorOrPort_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_cross_InteriorOrPort_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_cross_InteriorOrPort_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_cross_InteriorOrPort_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_cross_InteriorOrPort_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_cross_InteriorOrPort_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_cross_InteriorOrPort_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_cross_InteriorOrPort_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_cross_InteriorOrPort_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_cross_InteriorOrPort_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_cross_InteriorOrPort_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_cross_InteriorOrPort_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_cross_InteriorOrPort_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_cross_InteriorOrPort_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_cross_InteriorOrPort_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1270
    · have h := check_cross_InteriorOrPort_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case fan =>
    have hv : v.val<1054 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_fan_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_fan_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_fan_InteriorOrPort_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_fan_InteriorOrPort_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_fan_InteriorOrPort_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_fan_InteriorOrPort_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_fan_InteriorOrPort_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_fan_InteriorOrPort_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_fan_InteriorOrPort_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_fan_InteriorOrPort_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_fan_InteriorOrPort_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_fan_InteriorOrPort_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_fan_InteriorOrPort_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_fan_InteriorOrPort_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_fan_InteriorOrPort_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_fan_InteriorOrPort_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1054
    · have h := check_fan_InteriorOrPort_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case test =>
    have hv : v.val<114 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_test_InteriorOrPort_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<114
    · have h := check_test_InteriorOrPort_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
theorem edgeInterior_all (s : CellShape) (v : LocalPatch.Edge s) : EdgeInterior s v := by
  cases s
  case wireTop =>
    have hv : v.val<1313 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireTop_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireTop_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireTop_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireTop_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireTop_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireTop_EdgeInterior_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireTop_EdgeInterior_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireTop_EdgeInterior_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_wireTop_EdgeInterior_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_wireTop_EdgeInterior_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_wireTop_EdgeInterior_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_wireTop_EdgeInterior_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_wireTop_EdgeInterior_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_wireTop_EdgeInterior_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_wireTop_EdgeInterior_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_wireTop_EdgeInterior_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_wireTop_EdgeInterior_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_wireTop_EdgeInterior_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_wireTop_EdgeInterior_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1280
    · have h := check_wireTop_EdgeInterior_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1280 : v.val<1313
    · have h := check_wireTop_EdgeInterior_20 ⟨v.val-1280,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireBottom =>
    have hv : v.val<1313 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireBottom_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireBottom_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireBottom_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireBottom_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireBottom_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireBottom_EdgeInterior_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireBottom_EdgeInterior_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireBottom_EdgeInterior_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_wireBottom_EdgeInterior_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_wireBottom_EdgeInterior_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_wireBottom_EdgeInterior_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_wireBottom_EdgeInterior_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_wireBottom_EdgeInterior_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_wireBottom_EdgeInterior_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_wireBottom_EdgeInterior_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_wireBottom_EdgeInterior_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_wireBottom_EdgeInterior_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_wireBottom_EdgeInterior_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_wireBottom_EdgeInterior_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1280
    · have h := check_wireBottom_EdgeInterior_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1280 : v.val<1313
    · have h := check_wireBottom_EdgeInterior_20 ⟨v.val-1280,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireDown =>
    have hv : v.val<1313 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_wireDown_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_wireDown_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_wireDown_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_wireDown_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_wireDown_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_wireDown_EdgeInterior_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_wireDown_EdgeInterior_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_wireDown_EdgeInterior_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_wireDown_EdgeInterior_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_wireDown_EdgeInterior_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_wireDown_EdgeInterior_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_wireDown_EdgeInterior_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_wireDown_EdgeInterior_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_wireDown_EdgeInterior_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_wireDown_EdgeInterior_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_wireDown_EdgeInterior_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_wireDown_EdgeInterior_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_wireDown_EdgeInterior_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_wireDown_EdgeInterior_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1280
    · have h := check_wireDown_EdgeInterior_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1280 : v.val<1313
    · have h := check_wireDown_EdgeInterior_20 ⟨v.val-1280,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case cross =>
    have hv : v.val<3152 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_cross_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_cross_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_cross_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_cross_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_cross_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_cross_EdgeInterior_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_cross_EdgeInterior_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_cross_EdgeInterior_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_cross_EdgeInterior_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_cross_EdgeInterior_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_cross_EdgeInterior_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_cross_EdgeInterior_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_cross_EdgeInterior_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_cross_EdgeInterior_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_cross_EdgeInterior_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_cross_EdgeInterior_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_cross_EdgeInterior_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_cross_EdgeInterior_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_cross_EdgeInterior_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1280
    · have h := check_cross_EdgeInterior_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1280 : v.val<1344
    · have h := check_cross_EdgeInterior_20 ⟨v.val-1280,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1344 : v.val<1408
    · have h := check_cross_EdgeInterior_21 ⟨v.val-1344,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1408 : v.val<1472
    · have h := check_cross_EdgeInterior_22 ⟨v.val-1408,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1472 : v.val<1536
    · have h := check_cross_EdgeInterior_23 ⟨v.val-1472,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1536 : v.val<1600
    · have h := check_cross_EdgeInterior_24 ⟨v.val-1536,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1600 : v.val<1664
    · have h := check_cross_EdgeInterior_25 ⟨v.val-1600,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1664 : v.val<1728
    · have h := check_cross_EdgeInterior_26 ⟨v.val-1664,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1728 : v.val<1792
    · have h := check_cross_EdgeInterior_27 ⟨v.val-1728,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1792 : v.val<1856
    · have h := check_cross_EdgeInterior_28 ⟨v.val-1792,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1856 : v.val<1920
    · have h := check_cross_EdgeInterior_29 ⟨v.val-1856,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1920 : v.val<1984
    · have h := check_cross_EdgeInterior_30 ⟨v.val-1920,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1984 : v.val<2048
    · have h := check_cross_EdgeInterior_31 ⟨v.val-1984,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2048 : v.val<2112
    · have h := check_cross_EdgeInterior_32 ⟨v.val-2048,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2112 : v.val<2176
    · have h := check_cross_EdgeInterior_33 ⟨v.val-2112,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2176 : v.val<2240
    · have h := check_cross_EdgeInterior_34 ⟨v.val-2176,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2240 : v.val<2304
    · have h := check_cross_EdgeInterior_35 ⟨v.val-2240,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2304 : v.val<2368
    · have h := check_cross_EdgeInterior_36 ⟨v.val-2304,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2368 : v.val<2432
    · have h := check_cross_EdgeInterior_37 ⟨v.val-2368,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2432 : v.val<2496
    · have h := check_cross_EdgeInterior_38 ⟨v.val-2432,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2496 : v.val<2560
    · have h := check_cross_EdgeInterior_39 ⟨v.val-2496,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2560 : v.val<2624
    · have h := check_cross_EdgeInterior_40 ⟨v.val-2560,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2624 : v.val<2688
    · have h := check_cross_EdgeInterior_41 ⟨v.val-2624,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2688 : v.val<2752
    · have h := check_cross_EdgeInterior_42 ⟨v.val-2688,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2752 : v.val<2816
    · have h := check_cross_EdgeInterior_43 ⟨v.val-2752,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2816 : v.val<2880
    · have h := check_cross_EdgeInterior_44 ⟨v.val-2816,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2880 : v.val<2944
    · have h := check_cross_EdgeInterior_45 ⟨v.val-2880,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2944 : v.val<3008
    · have h := check_cross_EdgeInterior_46 ⟨v.val-2944,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h3008 : v.val<3072
    · have h := check_cross_EdgeInterior_47 ⟨v.val-3008,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h3072 : v.val<3136
    · have h := check_cross_EdgeInterior_48 ⟨v.val-3072,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h3136 : v.val<3152
    · have h := check_cross_EdgeInterior_49 ⟨v.val-3136,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case fan =>
    have hv : v.val<2619 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_fan_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_fan_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_fan_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_fan_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<320
    · have h := check_fan_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<384
    · have h := check_fan_EdgeInterior_5 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<448
    · have h := check_fan_EdgeInterior_6 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<512
    · have h := check_fan_EdgeInterior_7 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<576
    · have h := check_fan_EdgeInterior_8 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<640
    · have h := check_fan_EdgeInterior_9 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<704
    · have h := check_fan_EdgeInterior_10 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<768
    · have h := check_fan_EdgeInterior_11 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<832
    · have h := check_fan_EdgeInterior_12 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<896
    · have h := check_fan_EdgeInterior_13 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<960
    · have h := check_fan_EdgeInterior_14 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<1024
    · have h := check_fan_EdgeInterior_15 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1088
    · have h := check_fan_EdgeInterior_16 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1152
    · have h := check_fan_EdgeInterior_17 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1216
    · have h := check_fan_EdgeInterior_18 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1280
    · have h := check_fan_EdgeInterior_19 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1280 : v.val<1344
    · have h := check_fan_EdgeInterior_20 ⟨v.val-1280,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1344 : v.val<1408
    · have h := check_fan_EdgeInterior_21 ⟨v.val-1344,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1408 : v.val<1472
    · have h := check_fan_EdgeInterior_22 ⟨v.val-1408,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1472 : v.val<1536
    · have h := check_fan_EdgeInterior_23 ⟨v.val-1472,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1536 : v.val<1600
    · have h := check_fan_EdgeInterior_24 ⟨v.val-1536,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1600 : v.val<1664
    · have h := check_fan_EdgeInterior_25 ⟨v.val-1600,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1664 : v.val<1728
    · have h := check_fan_EdgeInterior_26 ⟨v.val-1664,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1728 : v.val<1792
    · have h := check_fan_EdgeInterior_27 ⟨v.val-1728,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1792 : v.val<1856
    · have h := check_fan_EdgeInterior_28 ⟨v.val-1792,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1856 : v.val<1920
    · have h := check_fan_EdgeInterior_29 ⟨v.val-1856,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1920 : v.val<1984
    · have h := check_fan_EdgeInterior_30 ⟨v.val-1920,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1984 : v.val<2048
    · have h := check_fan_EdgeInterior_31 ⟨v.val-1984,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2048 : v.val<2112
    · have h := check_fan_EdgeInterior_32 ⟨v.val-2048,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2112 : v.val<2176
    · have h := check_fan_EdgeInterior_33 ⟨v.val-2112,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2176 : v.val<2240
    · have h := check_fan_EdgeInterior_34 ⟨v.val-2176,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2240 : v.val<2304
    · have h := check_fan_EdgeInterior_35 ⟨v.val-2240,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2304 : v.val<2368
    · have h := check_fan_EdgeInterior_36 ⟨v.val-2304,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2368 : v.val<2432
    · have h := check_fan_EdgeInterior_37 ⟨v.val-2368,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2432 : v.val<2496
    · have h := check_fan_EdgeInterior_38 ⟨v.val-2432,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2496 : v.val<2560
    · have h := check_fan_EdgeInterior_39 ⟨v.val-2496,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h2560 : v.val<2619
    · have h := check_fan_EdgeInterior_40 ⟨v.val-2560,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case test =>
    have hv : v.val<272 := v.isLt
    by_cases h0 : v.val<64
    · have h := check_test_EdgeInterior_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<128
    · have h := check_test_EdgeInterior_1 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<192
    · have h := check_test_EdgeInterior_2 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<256
    · have h := check_test_EdgeInterior_3 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<272
    · have h := check_test_EdgeInterior_4 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
end PlanarHom.ColoringEmitter.MacroGeometry
