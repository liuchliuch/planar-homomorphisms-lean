import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def parentEdgeValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 277) else (if i < 3 then 155 else 252)) else (if i < 6 then (if i < 5 then 230 else 19) else (if i < 7 then 228 else 17))) else (if i < 12 then (if i < 10 then (if i < 9 then 3 else 243) else (if i < 11 then 1 else 8)) else (if i < 14 then (if i < 13 then 9 else 5) else (if i < 15 then 13 else 20)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 25 else 26) else (if i < 19 then 43 else 35)) else (if i < 22 then (if i < 21 then 41 else 45) else (if i < 23 then 24 else 33))) else (if i < 28 then (if i < 26 then (if i < 25 then 30 else 36) else (if i < 27 then 66 else 75)) else (if i < 30 then (if i < 29 then 70 else 61) else (if i < 31 then 58 else 72)))))

private def parentEdgeValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 68 else 59) else (if i < 35 then 57 else 62)) else (if i < 38 then (if i < 37 then 151 else 95) else (if i < 39 then 76 else 93))) else (if i < 44 then (if i < 42 then (if i < 41 then 94 else 79) else (if i < 43 then 229 else 77)) else (if i < 46 then (if i < 45 then 84 else 85) else (if i < 47 then 80 else 89)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 99 else 116) else (if i < 51 then 102 else 120)) else (if i < 54 then (if i < 53 then 111 else 108) else (if i < 55 then 122 else 100))) else (if i < 60 then (if i < 58 then (if i < 57 then 109 else 106) else (if i < 59 then 112 else 127)) else (if i < 62 then (if i < 61 then 128 else 145) else (if i < 63 then 137 else 143)))))

private def parentEdgeValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 147 else 126) else (if i < 67 then 135 else 132)) else (if i < 70 then (if i < 69 then 138 else 253) else (if i < 71 then 244 else 153))) else (if i < 76 then (if i < 74 then (if i < 73 then 242 else 161) else (if i < 75 then 237 else 235)) else (if i < 78 then (if i < 77 then 154 else 163) else (if i < 79 then 162 else 159)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 167 else 175) else (if i < 83 then 192 else 201)) else (if i < 86 then (if i < 85 then 196 else 187) else (if i < 87 then 184 else 198))) else (if i < 92 then (if i < 90 then (if i < 89 then 176 else 185) else (if i < 91 then 181 else 188)) else (if i < 94 then (if i < 93 then 203 else 204) else (if i < 95 then 221 else 226)))))

private def parentEdgeValue_b3 (i : ℕ) : ℕ :=
  (if i < 107 then (if i < 101 then (if i < 98 then (if i < 97 then 219 else 223) else (if i < 99 then 202 else (if i < 100 then 211 else 208))) else (if i < 104 then (if i < 102 then 215 else (if i < 103 then 234 else 238)) else (if i < 105 then 248 else (if i < 106 then 273 else 274)))) else (if i < 112 then (if i < 109 then (if i < 108 then 275 else 276) else (if i < 110 then 278 else (if i < 111 then 280 else 259))) else (if i < 115 then (if i < 113 then 263 else (if i < 114 then 269 else 272)) else (if i < 116 then 281 else (if i < 117 then 283 else 284)))))

private def parentEdgeValue_n0_0 (i : ℕ) : ℕ := if i < 32 then parentEdgeValue_b0 i else parentEdgeValue_b1 i

private def parentEdgeValue_n0_1 (i : ℕ) : ℕ := if i < 96 then parentEdgeValue_b2 i else parentEdgeValue_b3 i

private def parentEdgeValue_n1_0 (i : ℕ) : ℕ := if i < 64 then parentEdgeValue_n0_0 i else parentEdgeValue_n0_1 i

def parentEdgeValue (i : ℕ) : ℕ := parentEdgeValue_n1_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
