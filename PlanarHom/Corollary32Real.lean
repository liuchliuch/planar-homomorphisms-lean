import PlanarHom.Corollary32Field
import PlanarHom.ExtremalTransformAvailability

/-! Source-facing real-algebraic Corollary 3.2 interfaces. The original real
language determines its field/basis, and all numerical target values are literal
support, magnitude, sign and entrywise square. -/
noncomputable section
namespace PlanarHom.Corollary32
open Complexity Complexity.MixedCode AlgebraicProductInterpolation SupportTransformAvailability
variable {q u : ℕ}

/-- The original one-binary-type real language, retaining arbitrary fixed
algebraic unary companions and backgrounds. -/
def sourceLanguage (M : Matrix (Fin q) (Fin q) ℝ) (U : Fin u → Fin q → ℝ) (w : Fin q → ℝ)
    (hM : ∀ i j, IsAlgebraic ℚ (M i j)) (hU : ∀ l i, IsAlgebraic ℚ (U l i))
    (hw : ∀ i, IsAlgebraic ℚ (w i)) : RealLanguage q 1 u :=
  ⟨fun _ => M, U, w, fun _ => hM, hU, hw⟩

variable (L : RealLanguage q 1 u)

private theorem matrices_single : L.matricesK = fun _ : Fin 1 => L.matricesK 0 := by
  funext l
  exact congrArg L.matricesK (Subsingleton.elim _ _)

def mixedProblem : PromiseProblem := evaluationProblem L.basis
  (MagnitudeSign.mixedLanguage (L.matricesK 0)) L.unariesK L.weightsK

def squareProblem : PromiseProblem := evaluationProblem L.basis
  (fun _ : Fin 1 => fun i j => L.matricesK 0 i j ^ 2) L.unariesK L.weightsK

def supportProblem : PromiseProblem := evaluationProblem L.basis
  (fun _ : Fin 1 => MagnitudeSign.supportMatrix (L.matricesK 0)) L.unariesK L.weightsK

def magnitudeProblem : PromiseProblem := evaluationProblem L.basis
  (fun _ : Fin 1 => MagnitudeSign.magnitudeMatrix (L.matricesK 0)) L.unariesK L.weightsK

/-- Actual two-way reduction to the genuinely mixed two-constraint problem. -/
theorem mixed_equivalence :
    Nonempty (PromisePolyTimeTuringReduction L.problem (mixedProblem L)) ∧
    Nonempty (PromisePolyTimeTuringReduction (mixedProblem L) L.problem) := by
  have hM := matrices_single L
  constructor
  · unfold RealLanguage.problem mixedProblem
    rw [hM]
    exact ⟨MagnitudeSign.reverseMixedReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩
  · unfold RealLanguage.problem mixedProblem
    rw [hM]
    exact ⟨MagnitudeSign.forwardMixedReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩

/-- Both source weighted chains, with every isolated-vertex weight retained. -/
theorem support_chains :
    Nonempty (PromisePolyTimeTuringReduction (supportProblem L) (squareProblem L)) ∧
    Nonempty (PromisePolyTimeTuringReduction (squareProblem L) L.problem) ∧
    Nonempty (PromisePolyTimeTuringReduction (supportProblem L) (magnitudeProblem L)) ∧
    Nonempty (PromisePolyTimeTuringReduction (magnitudeProblem L) L.problem) := by
  refine ⟨⟨MagnitudeSign.supportSquareReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩, ?_,
    ⟨MagnitudeSign.supportMagnitudeReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩, ?_⟩
  · unfold RealLanguage.problem squareProblem
    rw [matrices_single L]
    exact ⟨squareReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩
  · unfold RealLanguage.problem magnitudeProblem
    rw [matrices_single L]
    exact ⟨MagnitudeSign.magnitudeReduction L.basis (L.matricesK 0) L.unariesK L.weightsK⟩

/-- All three auxiliary transforms coexist with the source constraint. -/
def joint_support_magnitude_sign := supportMagnitudeSign_joint L 0 L.problem
  (evaluationRefl L.basis L.matricesK L.unariesK L.weightsK)

/-- True extrema with their direct joint availability, without supplying
threshold values or an availability witness as extra hypotheses. -/
theorem joint_extremal_transforms (hne : L.matrices 0 ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∃ i j, |L.matrices 0 i j| = a) ∧
      (∃ i j, |L.matrices 0 i j| = b) ∧
      (∀ i j, L.matrices 0 i j ≠ 0 → a ≤ |L.matrices 0 i j|) ∧
      (∀ i j, |L.matrices 0 i j| ≤ b) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (L.mixedFiniteTargetProblem (fiveTransforms (L.matrices 0) a b) (fun i : Fin 0 => Fin.elim0 i)
          (fiveTransforms_algebraic _ a b (L.matrices_algebraic 0)) (fun i => Fin.elim0 i)) L.problem) := by
  obtain ⟨a,b,ha,hb,hia,hib,hmin,hmax⟩ := exists_actual_extrema (L.matrices 0) hne
  exact ⟨a,b,ha,hb,hia,hib,hmin,hmax,
    ⟨fiveTransforms_joint L 0 a b ha hb hmin hmax L.problem
      (evaluationRefl L.basis L.matricesK L.unariesK L.weightsK)⟩⟩

@[simp] theorem support_entry_coe (i j : Fin q) :
    (MagnitudeSign.supportMatrix (L.matricesK 0) i j : ℝ) =
      if L.matrices 0 i j = 0 then 0 else 1 := by
  simp only [MagnitudeSign.supportMatrix, MagnitudeSign.support_coe, RealLanguage.matricesK_coe]

@[simp] theorem magnitude_entry_coe (i j : Fin q) :
    (MagnitudeSign.magnitudeMatrix (L.matricesK 0) i j : ℝ) = |L.matrices 0 i j| := by
  simp only [MagnitudeSign.magnitudeMatrix, MagnitudeSign.magnitude_coe, RealLanguage.matricesK_coe]

@[simp] theorem sign_entry_coe (i j : Fin q) :
    (MagnitudeSign.signMatrix (L.matricesK 0) i j : ℝ) = Real.sign (L.matrices 0 i j) := by
  simp only [MagnitudeSign.signMatrix, MagnitudeSign.sign_coe, RealLanguage.matricesK_coe]

end PlanarHom.Corollary32
