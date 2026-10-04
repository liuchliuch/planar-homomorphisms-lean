import PlanarHom.ColoringMacroClockwiseCheck31
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_all (s : CellShape) (v : LocalPatch.NumericVertex s) : ClockwiseRow s v := by
  cases s
  case wireTop =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_wireTop_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_wireTop_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_wireTop_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<128
    · have h:=clockwise_wireTop_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<160
    · have h:=clockwise_wireTop_4 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h160 : v.val<192
    · have h:=clockwise_wireTop_5 ⟨v.val-160,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<224
    · have h:=clockwise_wireTop_6 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h224 : v.val<256
    · have h:=clockwise_wireTop_7 ⟨v.val-224,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<288
    · have h:=clockwise_wireTop_8 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h288 : v.val<320
    · have h:=clockwise_wireTop_9 ⟨v.val-288,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<352
    · have h:=clockwise_wireTop_10 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h352 : v.val<384
    · have h:=clockwise_wireTop_11 ⟨v.val-352,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<416
    · have h:=clockwise_wireTop_12 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h416 : v.val<448
    · have h:=clockwise_wireTop_13 ⟨v.val-416,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<480
    · have h:=clockwise_wireTop_14 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h480 : v.val<512
    · have h:=clockwise_wireTop_15 ⟨v.val-480,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h:=clockwise_wireTop_16 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireBottom =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_wireBottom_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_wireBottom_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_wireBottom_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<128
    · have h:=clockwise_wireBottom_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<160
    · have h:=clockwise_wireBottom_4 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h160 : v.val<192
    · have h:=clockwise_wireBottom_5 ⟨v.val-160,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<224
    · have h:=clockwise_wireBottom_6 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h224 : v.val<256
    · have h:=clockwise_wireBottom_7 ⟨v.val-224,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<288
    · have h:=clockwise_wireBottom_8 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h288 : v.val<320
    · have h:=clockwise_wireBottom_9 ⟨v.val-288,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<352
    · have h:=clockwise_wireBottom_10 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h352 : v.val<384
    · have h:=clockwise_wireBottom_11 ⟨v.val-352,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<416
    · have h:=clockwise_wireBottom_12 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h416 : v.val<448
    · have h:=clockwise_wireBottom_13 ⟨v.val-416,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<480
    · have h:=clockwise_wireBottom_14 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h480 : v.val<512
    · have h:=clockwise_wireBottom_15 ⟨v.val-480,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h:=clockwise_wireBottom_16 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case wireDown =>
    have hv : v.val<530 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_wireDown_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_wireDown_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_wireDown_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<128
    · have h:=clockwise_wireDown_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<160
    · have h:=clockwise_wireDown_4 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h160 : v.val<192
    · have h:=clockwise_wireDown_5 ⟨v.val-160,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<224
    · have h:=clockwise_wireDown_6 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h224 : v.val<256
    · have h:=clockwise_wireDown_7 ⟨v.val-224,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<288
    · have h:=clockwise_wireDown_8 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h288 : v.val<320
    · have h:=clockwise_wireDown_9 ⟨v.val-288,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<352
    · have h:=clockwise_wireDown_10 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h352 : v.val<384
    · have h:=clockwise_wireDown_11 ⟨v.val-352,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<416
    · have h:=clockwise_wireDown_12 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h416 : v.val<448
    · have h:=clockwise_wireDown_13 ⟨v.val-416,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<480
    · have h:=clockwise_wireDown_14 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h480 : v.val<512
    · have h:=clockwise_wireDown_15 ⟨v.val-480,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<530
    · have h:=clockwise_wireDown_16 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case cross =>
    have hv : v.val<1270 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_cross_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_cross_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_cross_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<128
    · have h:=clockwise_cross_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<160
    · have h:=clockwise_cross_4 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h160 : v.val<192
    · have h:=clockwise_cross_5 ⟨v.val-160,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<224
    · have h:=clockwise_cross_6 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h224 : v.val<256
    · have h:=clockwise_cross_7 ⟨v.val-224,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<288
    · have h:=clockwise_cross_8 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h288 : v.val<320
    · have h:=clockwise_cross_9 ⟨v.val-288,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<352
    · have h:=clockwise_cross_10 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h352 : v.val<384
    · have h:=clockwise_cross_11 ⟨v.val-352,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<416
    · have h:=clockwise_cross_12 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h416 : v.val<448
    · have h:=clockwise_cross_13 ⟨v.val-416,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<480
    · have h:=clockwise_cross_14 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h480 : v.val<512
    · have h:=clockwise_cross_15 ⟨v.val-480,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<544
    · have h:=clockwise_cross_16 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h544 : v.val<576
    · have h:=clockwise_cross_17 ⟨v.val-544,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<608
    · have h:=clockwise_cross_18 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h608 : v.val<640
    · have h:=clockwise_cross_19 ⟨v.val-608,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<672
    · have h:=clockwise_cross_20 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h672 : v.val<704
    · have h:=clockwise_cross_21 ⟨v.val-672,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<736
    · have h:=clockwise_cross_22 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h736 : v.val<768
    · have h:=clockwise_cross_23 ⟨v.val-736,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<800
    · have h:=clockwise_cross_24 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h800 : v.val<832
    · have h:=clockwise_cross_25 ⟨v.val-800,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<864
    · have h:=clockwise_cross_26 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h864 : v.val<896
    · have h:=clockwise_cross_27 ⟨v.val-864,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<928
    · have h:=clockwise_cross_28 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h928 : v.val<960
    · have h:=clockwise_cross_29 ⟨v.val-928,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<992
    · have h:=clockwise_cross_30 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h992 : v.val<1024
    · have h:=clockwise_cross_31 ⟨v.val-992,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1056
    · have h:=clockwise_cross_32 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1056 : v.val<1088
    · have h:=clockwise_cross_33 ⟨v.val-1056,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1088 : v.val<1120
    · have h:=clockwise_cross_34 ⟨v.val-1088,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1120 : v.val<1152
    · have h:=clockwise_cross_35 ⟨v.val-1120,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1152 : v.val<1184
    · have h:=clockwise_cross_36 ⟨v.val-1152,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1184 : v.val<1216
    · have h:=clockwise_cross_37 ⟨v.val-1184,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1216 : v.val<1248
    · have h:=clockwise_cross_38 ⟨v.val-1216,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1248 : v.val<1270
    · have h:=clockwise_cross_39 ⟨v.val-1248,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case fan =>
    have hv : v.val<1054 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_fan_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_fan_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_fan_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<128
    · have h:=clockwise_fan_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h128 : v.val<160
    · have h:=clockwise_fan_4 ⟨v.val-128,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h160 : v.val<192
    · have h:=clockwise_fan_5 ⟨v.val-160,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h192 : v.val<224
    · have h:=clockwise_fan_6 ⟨v.val-192,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h224 : v.val<256
    · have h:=clockwise_fan_7 ⟨v.val-224,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h256 : v.val<288
    · have h:=clockwise_fan_8 ⟨v.val-256,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h288 : v.val<320
    · have h:=clockwise_fan_9 ⟨v.val-288,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h320 : v.val<352
    · have h:=clockwise_fan_10 ⟨v.val-320,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h352 : v.val<384
    · have h:=clockwise_fan_11 ⟨v.val-352,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h384 : v.val<416
    · have h:=clockwise_fan_12 ⟨v.val-384,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h416 : v.val<448
    · have h:=clockwise_fan_13 ⟨v.val-416,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h448 : v.val<480
    · have h:=clockwise_fan_14 ⟨v.val-448,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h480 : v.val<512
    · have h:=clockwise_fan_15 ⟨v.val-480,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h512 : v.val<544
    · have h:=clockwise_fan_16 ⟨v.val-512,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h544 : v.val<576
    · have h:=clockwise_fan_17 ⟨v.val-544,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h576 : v.val<608
    · have h:=clockwise_fan_18 ⟨v.val-576,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h608 : v.val<640
    · have h:=clockwise_fan_19 ⟨v.val-608,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h640 : v.val<672
    · have h:=clockwise_fan_20 ⟨v.val-640,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h672 : v.val<704
    · have h:=clockwise_fan_21 ⟨v.val-672,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h704 : v.val<736
    · have h:=clockwise_fan_22 ⟨v.val-704,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h736 : v.val<768
    · have h:=clockwise_fan_23 ⟨v.val-736,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h768 : v.val<800
    · have h:=clockwise_fan_24 ⟨v.val-768,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h800 : v.val<832
    · have h:=clockwise_fan_25 ⟨v.val-800,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h832 : v.val<864
    · have h:=clockwise_fan_26 ⟨v.val-832,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h864 : v.val<896
    · have h:=clockwise_fan_27 ⟨v.val-864,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h896 : v.val<928
    · have h:=clockwise_fan_28 ⟨v.val-896,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h928 : v.val<960
    · have h:=clockwise_fan_29 ⟨v.val-928,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h960 : v.val<992
    · have h:=clockwise_fan_30 ⟨v.val-960,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h992 : v.val<1024
    · have h:=clockwise_fan_31 ⟨v.val-992,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h1024 : v.val<1054
    · have h:=clockwise_fan_32 ⟨v.val-1024,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
  case test =>
    have hv : v.val<114 := v.isLt
    by_cases h0 : v.val<32
    · have h:=clockwise_test_0 ⟨v.val-0,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h32 : v.val<64
    · have h:=clockwise_test_1 ⟨v.val-32,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h64 : v.val<96
    · have h:=clockwise_test_2 ⟨v.val-64,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    by_cases h96 : v.val<114
    · have h:=clockwise_test_3 ⟨v.val-96,by omega⟩
      convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
    omega
end PlanarHom.ColoringEmitter.MacroGeometry
