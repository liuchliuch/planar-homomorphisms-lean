import PlanarHom.SpectralAppendReduction
import PlanarHom.WeightedStretchAppend

/-! Actual spectral interpolation of weighted chains. The exterior diagonal
factors belong to the fixed matrices P; they are never treated as unit weights. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.PreparedSpectralRecovery
open Complexity Complexity.MixedCode ProductInterpolationPreparationMachines ProductCompatibility
variable {C K : Type} [Fintype C] [Field K] [DecidableEq K] {bt ut t : ℕ}

theorem preparation_recovery_of_spectral_queries
    (g : MixedCode) (hg : g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (P : Fin t → Matrix C C K) (a b : Fin t → K)
    (hzero : ∀ i,a i=0→b i=0) (hcompat : Compatible a b)
    (transform : ℕ → MixedCode → MixedCode) (answer : MixedCode → K)
    (hquery : ∀ n,1≤n→answer (transform n g)=
      g.evaluate hg (spectralLabels M selected P (fun i => a i^n)) U w) :
    recoverContext a ((MatrixFamilyInterpolationMachines.preparation a b selected.val transform g).1,
      (MatrixFamilyInterpolationMachines.preparation a b selected.val transform g).2.map answer) =
      g.evaluate hg (spectralLabels M selected P b) U w := by
  change recoverContext a (metadataFor a b (g.markedCount selected.val),
    (GraphInterpolationQueries.queries transform
      ((ExponentProductTables.representatives a b (g.markedCount selected.val)).length,g)).map answer) = _
  rw [PreparedRecoveryCorrectness.query_answers_ofFn]
  have he : (fun h : Fin (ExponentProductTables.representatives a b (g.markedCount selected.val)).length =>
      answer (transform (h.val+1) g)) =
      (fun h => g.evaluate hg (spectralLabels M selected P (fun i => a i^(h.val+1))) U w) := by
    funext h
    exact hquery (h.val+1) (by omega)
  rw [he]
  exact recover_spectral_computed g hg selected M U w P a b hzero hcompat

end PlanarHom.PreparedSpectralRecovery
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility PlanarHom.PreparedSpectralRecovery
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q bt ut t dimension : ℕ}

/-- Concrete ordinary path queries with the original background vector.
The spectral resolution is mathematical data, not an evaluator assumption. -/
def weightedSpectralAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (old : Fin bt) (P : Fin t → Matrix (Fin q) (Fin q) K) (a b : Fin t → K)
    (hchains : ∀ n : ℕ,0<n → weightedChain (M old) w n = ∑ i,a i^n • P i)
    (hzero : ∀ i,a i=0→b i=0) (hcompat : Compatible a b) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M (∑ i,b i • P i)) U w)
      (evaluationProblem basis M U w) := by
  let transform : ℕ → MixedCode → MixedCode := fun h g => g.stretchLabelLength bt old.val h
  apply MatrixFamilyInterpolationMachines.reductionOn basis a b bt transform
    (fp_stretchLabelLength bt old.val) (appendOne M (∑ i,b i • P i)) U w M U w
    (PlanarValid (bt+1) ut) (PlanarValid bt ut) (fun _ h=>h.1) (fun _ h=>h.1)
  · intro g hg h _
    exact g.stretchLabelLength_planar hg bt h old (g.appended_companion_bound hg.1)
  · intro g hg
    have hq : ∀ n,1≤n→totalEvaluation M U w (transform n g) =
        g.evaluate hg.1 (spectralLabels (appendOne M (M old)) (Fin.last bt) P (fun i=>a i^n)) U w := by
      intro n hn
      change totalEvaluation M U w (g.stretchLabelLength bt old.val n) = _
      rw [totalEvaluation_valid M U w _
        (g.stretchLabelLength_valid hg.1 bt n old (g.appended_companion_bound hg.1))]
      have hc := g.evaluate_stretchLabelLength_weighted hg.1 old n M U w
      have hde : Classical.decEq (Fin q) = instDecidableEqFin q := Subsingleton.elim _ _
      simp only [hde] at hc
      rw [hc,hchains n (by omega)]
      congr 1
      exact (replace_last_appendOne M (M old) _).symm
    have h := preparation_recovery_of_spectral_queries g hg.1 (Fin.last bt)
      (appendOne M (M old)) U w P a b hzero hcompat transform (totalEvaluation M U w) hq
    have hl : spectralLabels (appendOne M (M old)) (Fin.last bt) P b =
        appendOne M (∑ i,b i • P i) := replace_last_appendOne M (M old) _
    rw [hl] at h
    exact h

end PlanarHom.Complexity.MixedCode
