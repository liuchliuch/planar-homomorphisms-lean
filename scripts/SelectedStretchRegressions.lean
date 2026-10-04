import PlanarHom.SelectedStretchAppend

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode

private def mixedLoop : MixedCode :=
  ⟨2,[(0,0,2),(0,1,1),(1,0,2)],[(0,3),(0,3),(1,1)]⟩

private theorem mixedLoop_valid : mixedLoop.Valid 3 4 := by
  simp [MixedCode.Valid, mixedLoop]

example : (mixedLoop.stretchLabel 2 0 2).vertices=6 := by decide
example : (mixedLoop.stretchLabel 2 0 2).edges=
    [(0,2,0),(2,3,0),(3,0,0),(1,4,0),(4,5,0),(5,0,0),(0,1,1)] := by decide
example : (mixedLoop.stretchLabel 2 0 2).unaries=[(0,3),(0,3),(1,1)] := rfl
example : (mixedLoop.stretchLabelLength 2 0 3).edges=
    [(0,2,0),(2,3,0),(3,0,0),(1,4,0),(4,5,0),(5,0,0),(0,1,1)] := by decide
example : (mixedLoop.stretchLabelLength 2 0 1).edges=[(0,0,0),(1,0,0),(0,1,1)] := by decide
example : (mixedLoop.stretchLabelLength 2 0 0).edges=[(0,0,0),(1,0,0),(0,1,1)] := by decide
example : (mixedLoop.stretchLabel 9 0 5).vertices=2 := by decide
example : (mixedLoop.stretchLabel 9 0 5).edges=mixedLoop.edges := by decide

private def twoLoopOccurrences : MixedCode := ⟨1,[(0,0,1),(0,0,1)],[]⟩
example : (twoLoopOccurrences.stretchLabel 1 0 1).edges=
    [(0,1,0),(1,0,0),(0,2,0),(2,0,0)] := by decide

/-- Coincident path terminals compute the diagonal entry of the ordinary power. -/
example (M : Matrix (Fin 2) (Fin 2) ℚ) (n : ℕ) (i : Fin 2) :
    (∑ τ : Fin n → Fin 2, PathPower.weight n M i i τ)=(M^(n+1)) i i :=
  PathPower.sum_weight n M i i

example (M : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ) (U : Fin 4 → Fin 2 → ℚ) :
    (mixedLoop.stretchLabelLength 2 0 3).evaluate
      (mixedLoop.stretchLabelLength_valid mixedLoop_valid
        2 3 (0 : Fin 2) (mixedLoop.appended_companion_bound mixedLoop_valid)) M U (fun _ => 1) =
      mixedLoop.evaluate mixedLoop_valid (FiniteLanguageAliases.appendOne M (M 0^3)) U (fun _ => 1) :=
  mixedLoop.evaluate_stretchLabelLength_appendOne mixedLoop_valid (0 : Fin 2) 3 (by decide) M U
