import PlanarHom.MixedLabelExpansionReductions

/-! An actual single-query square-to-source reduction. Only the selected type
is doubled; every companion type, unary and background remains in place. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension a u d : ℕ}

def selectedSquareWord (selected : Fin a) (i : Fin a) : List (Fin a) :=
  if i=selected then [i,i] else [i]

def selectedSquareLanguage (M : Fin a→Matrix C C K) (selected : Fin a) : Fin a→Matrix C C K :=
  fun i x y => if i=selected then M i x y ^ 2 else M i x y

theorem wordMatrices_selectedSquare (M : Fin a→Matrix C C K) (selected : Fin a) :
    wordMatrices (selectedSquareWord selected) M=selectedSquareLanguage M selected := by
  funext i x y
  by_cases h : i=selected <;> simp [wordMatrices,selectedSquareWord,selectedSquareLanguage,h,pow_two]

def selectedSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin a→Matrix C C K) (selected : Fin a) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (selectedSquareLanguage M selected) U w)
      (evaluationProblem basis M U w) := by
  simpa only [wordMatrices_selectedSquare] using binaryWordExpansionReduction basis
    (selectedSquareWord selected) M U w

def domainSelectedSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin a→Matrix C C K) (selected : Fin a) (U : Fin u→C→K) (w : C→K) (D : Fin d→Set C)
    (B : Fin a→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (selectedSquareLanguage M selected) U w D B T)
      (domainEvaluationProblem basis M U w D B T) := by
  have hB : ∀i x y,B i x y→∀j∈selectedSquareWord selected i,B j x y := by
    intro i x y h j hj
    by_cases hi : i=selected
    · simp only [selectedSquareWord,if_pos hi,List.mem_cons,List.not_mem_nil,or_false,or_self] at hj
      simpa only [hj] using h
    · simp only [selectedSquareWord,if_neg hi,List.mem_singleton] at hj
      simpa only [hj] using h
  simpa only [wordMatrices_selectedSquare] using domainBinaryWordExpansionReduction basis
    (selectedSquareWord selected) M U w D B B T hB

theorem selectedSquareLanguage_single (M : Matrix C C K) :
    selectedSquareLanguage (fun _ : Fin 1 => M) 0=fun _ : Fin 1 => fun x y => M x y ^ 2 := by
  funext i x y
  have hi : i=0 := Subsingleton.elim _ _
  simp [selectedSquareLanguage,hi]

def squareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => fun x y => M x y ^ 2) U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) := by
  simpa only [selectedSquareLanguage_single] using selectedSquareReduction basis (fun _ : Fin 1 => M) 0 U w

def domainSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) (w : C→K) (D : Fin d→Set C)
    (E : Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => fun x y => M x y ^ 2) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) := by
  simpa only [selectedSquareLanguage_single] using domainSelectedSquareReduction basis
    (fun _ : Fin 1 => M) 0 U w D (fun _ => E) T

end
end PlanarHom.Complexity.MixedCode
