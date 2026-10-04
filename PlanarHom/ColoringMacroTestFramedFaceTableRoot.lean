import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def rootValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 1) else (if i < 3 then 2 else 3)) else (if i < 6 then (if i < 5 then 4 else 5) else (if i < 7 then 6 else 7))) else (if i < 12 then (if i < 10 then (if i < 9 then 16 else 17) else (if i < 11 then 18 else 19)) else (if i < 14 then (if i < 13 then 20 else 21) else (if i < 15 then 22 else 23)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 32 else 33) else (if i < 19 then 35 else 37)) else (if i < 22 then (if i < 21 then 39 else 48) else (if i < 23 then 49 else 51))) else (if i < 28 then (if i < 26 then (if i < 25 then 53 else 54) else (if i < 27 then 55 else 65)) else (if i < 30 then (if i < 29 then 66 else 67) else (if i < 31 then 68 else 69)))))

private def rootValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 71 else 87) else (if i < 35 then 100 else 101)) else (if i < 38 then (if i < 37 then 102 else 104) else (if i < 39 then 105 else 106))) else (if i < 44 then (if i < 42 then (if i < 41 then 107 else 116) else (if i < 43 then 118 else 119)) else (if i < 46 then (if i < 45 then 120 else 121) else (if i < 47 then 122 else 123)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 138 else 152) else (if i < 51 then 153 else 154)) else (if i < 54 then (if i < 53 then 155 else 156) else (if i < 55 then 157 else 158))) else (if i < 60 then (if i < 58 then (if i < 57 then 159 else 168) else (if i < 59 then 169 else 170)) else (if i < 62 then (if i < 61 then 171 else 172) else (if i < 63 then 173 else 174)))))

private def rootValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 175 else 184) else (if i < 67 then 185 else 187)) else (if i < 70 then (if i < 69 then 189 else 191) else (if i < 71 then 200 else 201))) else (if i < 76 then (if i < 74 then (if i < 73 then 203 else 205) else (if i < 75 then 206 else 207)) else (if i < 78 then (if i < 77 then 217 else 218) else (if i < 79 then 219 else 220)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 221 else 223) else (if i < 83 then 239 else 252)) else (if i < 86 then (if i < 85 then 253 else 254) else (if i < 87 then 256 else 257))) else (if i < 92 then (if i < 90 then (if i < 89 then 258 else 259) else (if i < 91 then 268 else 270)) else (if i < 94 then (if i < 93 then 271 else 272) else (if i < 95 then 273 else 274)))))

private def rootValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 275 else 290) else (if i < 99 then 304 else 305)) else (if i < 102 then (if i < 101 then 306 else 307) else (if i < 103 then 308 else 309))) else (if i < 108 then (if i < 106 then (if i < 105 then 310 else 311) else (if i < 107 then 320 else 321)) else (if i < 110 then (if i < 109 then 322 else 323) else (if i < 111 then 324 else 325)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 326 else 327) else (if i < 115 then 336 else 337)) else (if i < 118 then (if i < 117 then 339 else 341) else (if i < 119 then 343 else 352))) else (if i < 124 then (if i < 122 then (if i < 121 then 353 else 355) else (if i < 123 then 357 else 358)) else (if i < 126 then (if i < 125 then 359 else 369) else (if i < 127 then 370 else 371)))))

private def rootValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 372 else 373) else (if i < 131 then 375 else 391)) else (if i < 134 then (if i < 133 then 404 else 405) else (if i < 135 then 406 else 408))) else (if i < 140 then (if i < 138 then (if i < 137 then 409 else 410) else (if i < 139 then 411 else 420)) else (if i < 142 then (if i < 141 then 422 else 423) else (if i < 143 then 424 else 425)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 426 else 442) else (if i < 147 then 456 else 458)) else (if i < 150 then (if i < 149 then 460 else 461) else (if i < 151 then 470 else 472))) else (if i < 156 then (if i < 154 then (if i < 153 then 474 else 475) else (if i < 155 then 484 else 486)) else (if i < 158 then (if i < 157 then 488 else 489) else (if i < 159 then 499 else 508)))))

private def rootValue_b5 (i : ℕ) : ℕ :=
  (if i < 164 then (if i < 162 then (if i < 161 then 510 else 517) else (if i < 163 then 520 else 522)) else (if i < 166 then (if i < 165 then 529 else 532) else (if i < 167 then 534 else (if i < 168 then 541 else 569))))

private def rootValue_n0_0 (i : ℕ) : ℕ := if i < 32 then rootValue_b0 i else rootValue_b1 i

private def rootValue_n0_1 (i : ℕ) : ℕ := if i < 96 then rootValue_b2 i else rootValue_b3 i

private def rootValue_n0_2 (i : ℕ) : ℕ := if i < 160 then rootValue_b4 i else rootValue_b5 i

private def rootValue_n1_0 (i : ℕ) : ℕ := if i < 64 then rootValue_n0_0 i else rootValue_n0_1 i

private def rootValue_n2_0 (i : ℕ) : ℕ := if i < 128 then rootValue_n1_0 i else rootValue_n0_2 i

def rootValue (i : ℕ) : ℕ := rootValue_n2_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
