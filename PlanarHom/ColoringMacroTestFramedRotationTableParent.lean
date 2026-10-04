import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def parentValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 108) else (if i < 3 then 74 else 6)) else (if i < 6 then (if i < 5 then 41 else 4) else (if i < 7 then 42 else 6))) else (if i < 12 then (if i < 10 then (if i < 9 then 1 else 8) else (if i < 11 then 5 else 7)) else (if i < 14 then (if i < 13 then 7 else 5) else (if i < 15 then 7 else 4)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 7 else 7) else (if i < 19 then 17 else 8)) else (if i < 22 then (if i < 21 then 10 else 17) else (if i < 23 then 16 else 20))) else (if i < 28 then (if i < 26 then (if i < 25 then 7 else 8) else (if i < 27 then 12 else 3)) else (if i < 30 then (if i < 29 then 30 else 6) else (if i < 31 then 6 else 30)))))

private def parentValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 28 else 30) else (if i < 35 then 27 else 6)) else (if i < 38 then (if i < 37 then 60 else 38) else (if i < 39 then 0 else 40))) else (if i < 44 then (if i < 42 then (if i < 41 then 38 else 0) else (if i < 43 then 41 else 38)) else (if i < 46 then (if i < 45 then 40 else 40) else (if i < 47 then 0 else 40)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 38 else 43) else (if i < 51 then 40 else 53)) else (if i < 54 then (if i < 53 then 41 else 41) else (if i < 55 then 53 else 49))) else (if i < 60 then (if i < 58 then (if i < 57 then 53 else 40) else (if i < 59 then 41 else 42)) else (if i < 62 then (if i < 61 then 42 else 60) else (if i < 63 then 39 else 45)))))

private def parentValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 60 else 59) else (if i < 67 then 63 else 42)) else (if i < 70 then (if i < 69 then 39 else 75) else (if i < 71 then 8 else 76))) else (if i < 76 then (if i < 74 then (if i < 73 then 9 else 78) else (if i < 75 then 37 else 39)) else (if i < 78 then (if i < 77 then 74 else 75) else (if i < 79 then 75 else 74)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 75 else 71) else (if i < 83 then 76 else 77)) else (if i < 86 then (if i < 85 then 86 else 74) else (if i < 87 then 74 else 86))) else (if i < 92 then (if i < 90 then (if i < 89 then 82 else 86) else (if i < 91 then 82 else 74)) else (if i < 94 then (if i < 93 then 75 else 75) else (if i < 95 then 93 else 69)))))

private def parentValue_b3 (i : ℕ) : ℕ :=
  (if i < 107 then (if i < 101 then (if i < 98 then (if i < 97 then 78 else 93) else (if i < 99 then 92 else (if i < 100 then 96 else 75))) else (if i < 104 then (if i < 102 then 96 else (if i < 103 then 41 else 37)) else (if i < 105 then 8 else (if i < 106 then 106 else 0)))) else (if i < 112 then (if i < 109 then (if i < 108 then 0 else 107) else (if i < 110 then 1 else (if i < 111 then 2 else 106))) else (if i < 115 then (if i < 113 then 41 else (if i < 114 then 8 else 105)) else (if i < 116 then 2 else (if i < 117 then 117 else 114)))))

private def parentValue_n0_0 (i : ℕ) : ℕ := if i < 32 then parentValue_b0 i else parentValue_b1 i

private def parentValue_n0_1 (i : ℕ) : ℕ := if i < 96 then parentValue_b2 i else parentValue_b3 i

private def parentValue_n1_0 (i : ℕ) : ℕ := if i < 64 then parentValue_n0_0 i else parentValue_n0_1 i

def parentValue (i : ℕ) : ℕ := parentValue_n1_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
