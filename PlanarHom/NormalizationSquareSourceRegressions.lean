import PlanarHom.RectangularSquareNormSource

/-! Boundary and consumer-call regression theorems, newly written. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.NormalizationSourceRegressions
open Complexity Complexity.MixedCode FixedSquareNormSource
open RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation

/-- The internal vertex's weight is counted. -/
theorem singleton_weighted_square :
    squareNorm (fun _ _ : Fin 1 => (2 : ℚ)) (fun _ => 3) 0 = 12 := by
  norm_num [squareNorm]

/-- Unequal rectangular sides: 7*2² + 11*3² = 127. -/
theorem unequal_left_square :
    squareNorm (block (fun (_ : Fin 1) (j : Fin 2) => if j = 0 then (2 : ℚ) else 3))
      (weights (fun _ => 5) (fun j => if j = 0 then 7 else 11)) 0 = 127 := by
  change squareNorm _ _ (Fin.castAdd 2 (0 : Fin 1)) = _
  rw [squareNorm_left]
  norm_num [Fin.sum_univ_two]

theorem unequal_right_squares :
    squareNorm (block (fun (_ : Fin 1) (j : Fin 2) => if j = 0 then (2 : ℚ) else 3))
      (weights (fun _ => 5) (fun j => if j = 0 then 7 else 11)) 1 = 20 ∧
    squareNorm (block (fun (_ : Fin 1) (j : Fin 2) => if j = 0 then (2 : ℚ) else 3))
      (weights (fun _ => 5) (fun j => if j = 0 then 7 else 11)) 2 = 45 := by
  constructor
  · change squareNorm _ _ (Fin.natAdd 1 (0 : Fin 2)) = _
    rw [squareNorm_right]
    norm_num
  · change squareNorm _ _ (Fin.natAdd 1 (1 : Fin 2)) = _
    rw [squareNorm_right]
    norm_num

theorem zeroth_background {C K : Type} [Fintype C] [CommSemiring K]
    (B : Matrix C C K) (w : C → K) :
    (fun i => w i * (squareNorm B w i)^0) = w := by simp

theorem empty_right_square (V : Matrix (Fin 2) (Fin 0) ℚ) (μ : Fin 2 → ℚ) (i : Fin 2) :
    squareNorm (block V) (weights μ (fun j => j.elim0)) (Fin.castAdd 0 i) = 0 := by
  rw [squareNorm_left]
  simp

theorem empty_left_square (V : Matrix (Fin 0) (Fin 3) ℚ) (ν : Fin 3 → ℚ) (j : Fin 3) :
    squareNorm (block V) (weights (fun i => i.elim0) ν) (Fin.natAdd 0 j) = 0 := by
  rw [squareNorm_right]
  simp

/-- No positivity/nonemptiness assumptions are added to the fixed-moment program. -/
theorem empty_side_program {K : IntermediateField ℚ ℝ} {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (V : Matrix (Fin 0) (Fin 3) K)
    (μ : Fin 0 → K) (ν : Fin 3 → K) (m : ℕ) :
    Nonempty (PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0)
        (fun i => weights μ ν i * (squareNorm (block V) (weights μ ν) i)^m))
      (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν))) :=
  ⟨rectangularMomentReduction basis V μ ν m⟩

def emptyGraph : MixedCode := ⟨0, [], []⟩
def isolate : MixedCode := ⟨1, [], []⟩
def loopGraph : MixedCode := ⟨1, [(0,0,0)], []⟩
def parallelGraph : MixedCode := ⟨2, [(0,1,0),(0,1,0)], []⟩

theorem emptyGraph_valid : emptyGraph.Valid 1 0 := by simp [MixedCode.Valid, emptyGraph]
theorem isolate_valid : isolate.Valid 1 0 := by simp [MixedCode.Valid, isolate]
theorem loopGraph_valid : loopGraph.Valid 1 0 := by simp [MixedCode.Valid, loopGraph]
theorem parallelGraph_valid : parallelGraph.Valid 1 0 := by simp [MixedCode.Valid, parallelGraph]

theorem empty_loop_insertion : emptyGraph.addLoops 0 = emptyGraph := rfl

theorem isolate_gets_one_factor : (isolate.addLoops 0).edges = [(0,0,0)] := rfl

theorem old_loop_is_retained : (loopGraph.addLoops 0).edges = [(0,0,0),(0,0,0)] := rfl

theorem parallel_occurrences_retained :
    (parallelGraph.addLoops 0).edges = [(0,1,0),(0,1,0),(1,1,0),(0,0,0)] := rfl

theorem empty_evaluation {C : Type} [Fintype C] (B : Matrix C C ℚ) (w : C → ℚ) :
    emptyGraph.evaluate emptyGraph_valid (fun _ => B) (fun l : Fin 0 => l.elim0) w = 1 := by
  simp [MixedCode.evaluate, emptyGraph]

theorem isolate_weight_not_dropped :
    isolate.evaluate isolate_valid (fun (_ : Fin 1) (_ _ : Fin 1) => (2 : ℚ))
      (fun l : Fin 0 => l.elim0) (fun i => 3 *
        (squareNorm (fun _ _ : Fin 1 => (2 : ℚ)) (fun _ => 3) i)^1) = 36 := by
  norm_num [MixedCode.evaluate, isolate, squareNorm]

theorem loop_moment_semantics :
    loopGraph.evaluate loopGraph_valid (fun (_ : Fin 1) (_ _ : Fin 1) => (2 : ℚ))
      (fun l : Fin 0 => l.elim0) (fun i => 3 *
        (squareNorm (fun _ _ : Fin 1 => (2 : ℚ)) (fun _ => 3) i)^1) = 72 := by
  norm_num [MixedCode.evaluate, loopGraph, squareNorm, binaryValue]

theorem parallel_moment_semantics :
    parallelGraph.evaluate parallelGraph_valid (fun (_ : Fin 1) (_ _ : Fin 1) => (2 : ℚ))
      (fun l : Fin 0 => l.elim0) (fun i => 3 *
        (squareNorm (fun _ _ : Fin 1 => (2 : ℚ)) (fun _ => 3) i)^1) = 5184 := by
  norm_num [MixedCode.evaluate, parallelGraph, squareNorm, binaryValue]

/-- The literal original consumer's call order is accepted by the new lemma. -/
theorem quotient_moment_consumer_call {p s : ℕ} {K F : IntermediateField ℚ ℝ}
    (h₀ : K ≤ F) (V : Matrix (Fin p) (Fin s) K) (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ))
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (hc : ∀ i j, (C i j : ℝ) = block
      (RectangularWeightedNormNormalization.normalized (realRectangular V)
        (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) i j)
    (m : ℕ) (z : Quotient (Twins.rowSetoid C)) :
    ((Twins.quotientWeight C (fun i => IntermediateField.inclusion h₀ (weights μ ν i) *
      (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m) z : F) : ℝ) =
      Twins.quotientWeight
        (block (RectangularWeightedNormNormalization.normalized (realRectangular V)
          (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))))
        (fun i => ((weights μ ν i : K) : ℝ) *
          (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)^(2*m))
        (FiniteFieldQuotientLanguage.realQuotientEquiv C _ hc z) :=
  quotient_moment_real h₀ V μ ν (fun i => (hμ i).le) (fun j => (hν j).le) C hc m z

end PlanarHom.NormalizationSourceRegressions
