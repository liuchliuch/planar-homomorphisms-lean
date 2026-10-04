import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def vertexRootValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 549 else 555) else (if i < 3 then 561 else 498)) else (if i < 6 then (if i < 5 then 461 else 46) else (if i < 7 then 505 else 35))) else (if i < 12 then (if i < 10 then (if i < 9 then 64 else 485) else (if i < 11 then 80 else 24)) else (if i < 14 then (if i < 13 then 132 else 11) else (if i < 15 then 29 else 43)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 50 else 53) else (if i < 19 then 85 else 96)) else (if i < 22 then (if i < 21 then 89 else 91) else (if i < 23 then 56 else 95))) else (if i < 28 then (if i < 26 then (if i < 25 then 61 else 77) else (if i < 27 then 110 else 150)) else (if i < 30 then (if i < 29 then 138 else 148) else (if i < 31 then 126 else 146)))))

private def vertexRootValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 107 else 120) else (if i < 35 then 113 else 131)) else (if i < 38 then (if i < 37 then 301 else 475) else (if i < 39 then 190 else 478))) else (if i < 44 then (if i < 42 then (if i < 41 then 196 else 157) else (if i < 43 then 182 else 155)) else (if i < 46 then (if i < 45 then 168 else 286) else (if i < 47 then 163 else 179)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 193 else 202) else (if i < 51 then 214 else 237)) else (if i < 54 then (if i < 53 then 248 else 235) else (if i < 55 then 243 else 200))) else (if i < 60 then (if i < 58 then (if i < 57 then 219 else 213) else (if i < 59 then 227 else 285)) else (if i < 62 then (if i < 61 then 294 else 292) else (if i < 63 then 274 else 269)))))

private def vertexRootValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 298 else 288) else (if i < 67 then 280 else 261)) else (if i < 70 then (if i < 69 then 277 else 506) else (if i < 71 then 490 else 341))) else (if i < 76 then (if i < 74 then (if i < 73 then 428 else 330) else (if i < 75 then 310 else 480)) else (if i < 78 then (if i < 77 then 386 else 401) else (if i < 79 then 436 else 317)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 329 else 349) else (if i < 83 then 362 else 394)) else (if i < 86 then (if i < 85 then 392 else 374) else (if i < 87 then 370 else 398))) else (if i < 92 then (if i < 90 then (if i < 89 then 359 else 372) else (if i < 91 then 367 else 377)) else (if i < 94 then (if i < 93 then 406 else 409) else (if i < 95 then 441 else 452)))))

private def vertexRootValue_b3 (i : ℕ) : ℕ :=
  (if i < 107 then (if i < 101 then (if i < 98 then (if i < 97 then 445 else 447) else (if i < 99 then 412 else (if i < 100 then 451 else 417))) else (if i < 104 then (if i < 102 then 433 else (if i < 103 then 467 else 483)) else (if i < 105 then 495 else (if i < 106 then 545 else 547)))) else (if i < 112 then (if i < 109 then (if i < 108 then 551 else 553) else (if i < 110 then 557 else (if i < 111 then 559 else 515))) else (if i < 115 then (if i < 113 then 527 else (if i < 114 then 539 else 569)) else (if i < 116 then 563 else (if i < 117 then 566 else 567)))))

private def vertexRootValue_n0_0 (i : ℕ) : ℕ := if i < 32 then vertexRootValue_b0 i else vertexRootValue_b1 i

private def vertexRootValue_n0_1 (i : ℕ) : ℕ := if i < 96 then vertexRootValue_b2 i else vertexRootValue_b3 i

private def vertexRootValue_n1_0 (i : ℕ) : ℕ := if i < 64 then vertexRootValue_n0_0 i else vertexRootValue_n0_1 i

def vertexRootValue (i : ℕ) : ℕ := vertexRootValue_n1_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
