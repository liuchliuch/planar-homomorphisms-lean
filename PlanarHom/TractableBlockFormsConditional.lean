/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.TractableBlockFormsDefinition
import PlanarHom.BooleanTensorEasyAssembly
import PlanarHom.TractableRankOneBlockSourceConditional
import PlanarHom.BipartiteRankTwoTractabilitySourceConditional

/-! Literal structural hypotheses and the complete algorithmic conclusion of
source Proposition 2.6. A block chart supplies only the displayed real matrix
identity, not an algorithm, field membership for individual amplitudes, or a
complexity certificate. The dimensions and positive parameters vary by block. -/
noncomputable section
open Classical
namespace PlanarHom.TractableBlockComposition
open Complexity Complexity.MixedCode IsingTensorTractability

variable {C B : Type} [Fintype C] [Fintype B] {dimension : ℕ}

/-- Every displayed block is computed in the original prescribed finite real
field, even when the displayed rank-one square roots initially lie outside it. -/
theorem form_inFP_of_ising (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀)
    (hform : Form (fun i j => (M i j : ℝ))) :
    (evaluationProblem basis (fun _ : Fin 1 => M) emptyUnaries (fun _ => 1)).InFP := by
  cases hform with
  | zero e hz =>
    have hm : M = 0 := by
      funext i j
      apply Subtype.ext
      exact congrArg (fun A : Matrix C C ℝ => A i j) hz
    have hf := color_inFP basis e _
      (RankOneEvaluationMachine.evaluation_inFP basis (fun _ : Fin 1 => (0 : K₀)) (fun _ => 1))
    simpa only [hm, zero_mul, Matrix.zero_apply] using hf
  | rankOne i0 e a ha ρ hρ hsource =>
    exact source_rankOne_ising_tensor_inFP_of_ising hIsing K₀ basis M i0 e a ha ρ hρ hsource
  | bipartite i0 j0 e a ha b hb ρ hρ hsource =>
    exact BipartiteRankTwoTractability.source_ising_tensor_inFP_of_ising hIsing K₀ basis
      M i0 j0 e a ha b hb ρ hρ hsource

/-- Source Proposition2.6 in any prescribed original finite-field codec.
A fixed partition of the colors is the simultaneous row/column direct-sum
chart; no algorithmic hypothesis is present in any block or in the conclusion. -/
theorem proposition26_of_ising (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀)
    (hs : ∀ i j, M i j = M j i) (block : C → B)
    (hzero : ∀ i j, block i ≠ block j → M i j = 0)
    (hform : ∀ b : B, Form (fun i j : {i // block i = b} => (M i.val j.val : ℝ))) :
    (evaluationProblem basis (fun _ : Fin 1 => M) emptyUnaries (fun _ => 1)).InFP := by
  exact fibers_inFP basis block M hs hzero (fun _ => 1)
    (fun b => form_inFP_of_ising hIsing K₀ basis (fun i j : {i // block i = b} => M i.val j.val) (hform b))

end PlanarHom.TractableBlockComposition

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode IsingTensorTractability TractableBlockComposition
variable {q r : ℕ} (L : RealLanguage q 1 0)

/-- Literal real-algebraic source endpoint. Unit background, color permutation,
fixed finite direct sum, all displayed parameters positive, and the exact
original source basis match Proposition2.6. -/
theorem proposition26_of_ising (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (hunit : ∀ i, L.weights i = 1)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i) (block : Fin q → Fin r)
    (hzero : ∀ i j, block i ≠ block j → L.matrices 0 i j = 0)
    (hform : ∀ b : Fin r, Form (fun i j : {i // block i = b} => L.matrices 0 i.val j.val)) :
    L.problem.InFP := by
  have hf := TractableBlockComposition.proposition26_of_ising hIsing L.field L.basis (L.matricesK 0)
    (fun i j => Subtype.ext (hs i j)) block (fun i j h => Subtype.ext (hzero i j h)) hform
  have hM : L.matricesK = fun _ : Fin 1 => L.matricesK 0 := by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim l 0)
  have hU : L.unariesK = (emptyUnaries : Fin 0 → Fin q → L.field) := by
    funext l
    exact Fin.elim0 l
  have hw : L.weightsK = fun _ => 1 := by
    funext i
    exact Subtype.ext (hunit i)
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hM,hU,hw]
  exact hf

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
