import PlanarHom.ColoringTestMacroRowsChecks1
noncomputable section
namespace PlanarHom.ColoringTestMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_all (v : Vertex) : VertexGood v := by
  have hv : v.val<114 := v.isLt
  by_cases h0 : v.val<64
  · have h := VertexGood_0 ⟨v.val-0,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  by_cases h64 : v.val<114
  · have h := VertexGood_1 ⟨v.val-64,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  omega
theorem DartGood_all (v : Edge) : DartGood v := by
  have hv : v.val<272 := v.isLt
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
  by_cases h256 : v.val<272
  · have h := DartGood_4 ⟨v.val-256,by omega⟩
    convert h using 1 <;> apply Fin.ext <;> dsimp <;> omega
  omega
def certificate : GeometricRowCertificate graph row where
  nodup v := (VertexGood_all v).1
  host v := (VertexGood_all v).2
  position := position
  cover a := DartGood_all a.1 a.2

def rows : RotationRows graph := certificate.rows
end PlanarHom.ColoringTestMacroRows
