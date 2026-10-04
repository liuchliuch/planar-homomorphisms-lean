import PlanarHom.PreparedSpectralRecovery
import PlanarHom.SelectedStretchAppend
import PlanarHom.FiniteLanguageJointReductions

/-! Actual unit-background joint spectral interpolation. The source matrix
occurrences remain alongside the appended target. Every query is an actual
positive-length path transformation submitted to the original source alphabet. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
open PlanarHom.MatrixFamilyInterpolationMachines PlanarHom.PreparedSpectralRecovery
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q bt ut t dimension : ℕ}

theorem replace_last_appendOne {X : Type} (M : Fin bt → X) (C D : X) :
    (fun l : Fin (bt+1) => if l=Fin.last bt then D else appendOne M C l) = appendOne M D := by
  funext l
  by_cases hl : l=Fin.last bt
  · subst l
    simp [appendOne_aux]
  · rw [if_neg hl]
    exact appendOne_eq_of_ne_aux M C D l (fun h => hl (Fin.ext h))

/-- All bit algorithms are concrete. The remaining premises are only the
mathematical spectral resolution and the scalar product-map hypotheses. -/
def spectralAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (P : Fin t → Matrix (Fin q) (Fin q) K) (a b : Fin t → K)
    (hpowers : ∀ n : ℕ, 0<n → M old ^ n = ∑ i, a i ^ n • P i)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (∑ i, b i • P i)) U (fun _ => 1))
      (evaluationProblem basis M U (fun _ => 1)) := by
  let transform : ℕ → MixedCode → MixedCode := fun h g => g.stretchLabelLength bt old.val h
  apply MatrixFamilyInterpolationMachines.reductionOn basis a b bt transform
    (fp_stretchLabelLength bt old.val)
    (appendOne M (∑ i, b i • P i)) U (fun _ => 1) M U (fun _ => 1)
    (PlanarValid (bt+1) ut) (PlanarValid bt ut) (fun _ h => h.1) (fun _ h => h.1)
  · intro g hg h _
    exact g.stretchLabelLength_planar hg bt h old (g.appended_companion_bound hg.1)
  · intro g hg
    have hq : ∀ n, 1≤n → totalEvaluation M U (fun _ => (1 : K)) (transform n g) =
        g.evaluate hg.1 (fun l => if l=Fin.last bt then M old ^ n else appendOne M (M old) l) U (fun _ => 1) := by
      intro n hn
      rw [replace_last_appendOne]
      change totalEvaluation M U (fun _ => 1) (g.stretchLabelLength bt old.val n) = _
      rw [totalEvaluation_valid M U (fun _ => 1) _
        (g.stretchLabelLength_valid hg.1 bt n old (g.appended_companion_bound hg.1))]
      have hde : Classical.decEq (Fin q) = instDecidableEqFin q := Subsingleton.elim _ _
      simpa only [hde] using g.evaluate_stretchLabelLength_appendOne hg.1 old n hn M U
    have h := preparation_recovery_of_matrix_power_queries g hg.1 (Fin.last bt)
      (appendOne M (M old)) U (fun _ => 1) P (M old) a b hpowers hzero hcompat transform
      (totalEvaluation M U (fun _ => 1)) hq
    have hlabels : spectralLabels (appendOne M (M old)) (Fin.last bt) P b =
        appendOne M (∑ i, b i • P i) := replace_last_appendOne M (M old) _
    rw [hlabels] at h
    exact h

/-- The original source availability witness is composed only after the
concrete source-alphabet queries have been built and verified. -/
def spectralAppend_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (P : Fin t → Matrix (Fin q) (Fin q) K) (a b : Fin t → K)
    (hpowers : ∀ n : ℕ, 0<n → M old ^ n = ∑ i, a i ^ n • P i)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (evaluationProblem basis M U (fun _ => 1)) base) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (∑ i, b i • P i)) U (fun _ => 1)) base :=
  (spectralAppendReduction basis M U old P a b hpowers hzero hcompat).trans available

end PlanarHom.Complexity.MixedCode
