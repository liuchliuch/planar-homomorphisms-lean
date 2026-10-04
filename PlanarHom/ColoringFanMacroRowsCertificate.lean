import PlanarHom.ColoringFanMacroRowsChecks14
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_all (v : Vertex) : VertexGood v := by
  have hv : v.val<1054 := v.isLt
  by_cases h0 : v.val<64
  · have h := VertexGood_0 ⟨v.val-0,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h64 : v.val<128
  · have h := VertexGood_1 ⟨v.val-64,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h128 : v.val<192
  · have h := VertexGood_2 ⟨v.val-128,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h192 : v.val<256
  · have h := VertexGood_3 ⟨v.val-192,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h256 : v.val<320
  · have h := VertexGood_4 ⟨v.val-256,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h320 : v.val<384
  · have h := VertexGood_5 ⟨v.val-320,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h384 : v.val<448
  · have h := VertexGood_6 ⟨v.val-384,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h448 : v.val<512
  · have h := VertexGood_7 ⟨v.val-448,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h512 : v.val<576
  · have h := VertexGood_8 ⟨v.val-512,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h576 : v.val<640
  · have h := VertexGood_9 ⟨v.val-576,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h640 : v.val<704
  · have h := VertexGood_10 ⟨v.val-640,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h704 : v.val<768
  · have h := VertexGood_11 ⟨v.val-704,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h768 : v.val<832
  · have h := VertexGood_12 ⟨v.val-768,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h832 : v.val<896
  · have h := VertexGood_13 ⟨v.val-832,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h896 : v.val<960
  · have h := VertexGood_14 ⟨v.val-896,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h960 : v.val<1024
  · have h := VertexGood_15 ⟨v.val-960,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1024 : v.val<1054
  · have h := VertexGood_16 ⟨v.val-1024,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  omega
theorem DartGood_all (v : Edge) : DartGood v := by
  have hv : v.val<2619 := v.isLt
  by_cases h0 : v.val<64
  · have h := DartGood_0 ⟨v.val-0,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h64 : v.val<128
  · have h := DartGood_1 ⟨v.val-64,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h128 : v.val<192
  · have h := DartGood_2 ⟨v.val-128,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h192 : v.val<256
  · have h := DartGood_3 ⟨v.val-192,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h256 : v.val<320
  · have h := DartGood_4 ⟨v.val-256,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h320 : v.val<384
  · have h := DartGood_5 ⟨v.val-320,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h384 : v.val<448
  · have h := DartGood_6 ⟨v.val-384,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h448 : v.val<512
  · have h := DartGood_7 ⟨v.val-448,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h512 : v.val<576
  · have h := DartGood_8 ⟨v.val-512,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h576 : v.val<640
  · have h := DartGood_9 ⟨v.val-576,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h640 : v.val<704
  · have h := DartGood_10 ⟨v.val-640,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h704 : v.val<768
  · have h := DartGood_11 ⟨v.val-704,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h768 : v.val<832
  · have h := DartGood_12 ⟨v.val-768,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h832 : v.val<896
  · have h := DartGood_13 ⟨v.val-832,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h896 : v.val<960
  · have h := DartGood_14 ⟨v.val-896,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h960 : v.val<1024
  · have h := DartGood_15 ⟨v.val-960,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1024 : v.val<1088
  · have h := DartGood_16 ⟨v.val-1024,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1088 : v.val<1152
  · have h := DartGood_17 ⟨v.val-1088,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1152 : v.val<1216
  · have h := DartGood_18 ⟨v.val-1152,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1216 : v.val<1280
  · have h := DartGood_19 ⟨v.val-1216,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1280 : v.val<1344
  · have h := DartGood_20 ⟨v.val-1280,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1344 : v.val<1408
  · have h := DartGood_21 ⟨v.val-1344,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1408 : v.val<1472
  · have h := DartGood_22 ⟨v.val-1408,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1472 : v.val<1536
  · have h := DartGood_23 ⟨v.val-1472,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1536 : v.val<1600
  · have h := DartGood_24 ⟨v.val-1536,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1600 : v.val<1664
  · have h := DartGood_25 ⟨v.val-1600,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1664 : v.val<1728
  · have h := DartGood_26 ⟨v.val-1664,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1728 : v.val<1792
  · have h := DartGood_27 ⟨v.val-1728,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1792 : v.val<1856
  · have h := DartGood_28 ⟨v.val-1792,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1856 : v.val<1920
  · have h := DartGood_29 ⟨v.val-1856,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1920 : v.val<1984
  · have h := DartGood_30 ⟨v.val-1920,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h1984 : v.val<2048
  · have h := DartGood_31 ⟨v.val-1984,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2048 : v.val<2112
  · have h := DartGood_32 ⟨v.val-2048,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2112 : v.val<2176
  · have h := DartGood_33 ⟨v.val-2112,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2176 : v.val<2240
  · have h := DartGood_34 ⟨v.val-2176,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2240 : v.val<2304
  · have h := DartGood_35 ⟨v.val-2240,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2304 : v.val<2368
  · have h := DartGood_36 ⟨v.val-2304,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2368 : v.val<2432
  · have h := DartGood_37 ⟨v.val-2368,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2432 : v.val<2496
  · have h := DartGood_38 ⟨v.val-2432,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2496 : v.val<2560
  · have h := DartGood_39 ⟨v.val-2496,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h2560 : v.val<2619
  · have h := DartGood_40 ⟨v.val-2560,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  omega
def certificate : GeometricRowCertificate graph row where
  nodup v := (VertexGood_all v).1
  host v := (VertexGood_all v).2
  position := position
  cover a := DartGood_all a.1 a.2

def rows : RotationRows graph := certificate.rows
end PlanarHom.ColoringFanMacroRows
