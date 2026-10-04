import PlanarHom.SpectralInterpolationRecovery
import PlanarHom.MatrixFamilyInterpolationMachines
import PlanarHom.PreparedRecoveryCorrectness

/-! The genuine compiled recovery function applied to computed spectral rows
and the actual positive query list, with no supplied class/recovery oracle. -/
noncomputable section
namespace PlanarHom.PreparedSpectralRecovery
open Complexity Complexity.MixedCode ProductInterpolationPreparationMachines
open ProductCompatibility LagrangeRecoveryListSemantics
variable {C K : Type} [Fintype C] [Field K] [DecidableEq K]
variable {bt ut t : ℕ}

theorem recover_spectral_computed (g : MixedCode) (hg : g.Valid bt ut)
    (selected : Fin bt) (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (P : Fin t → Matrix C C K) (a b : Fin t → K)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b) :
    recoverContext a (metadataFor a b (g.markedCount selected.val),
      List.ofFn (fun h : Fin (ExponentProductTables.representatives a b (g.markedCount selected.val)).length =>
        g.evaluate hg (spectralLabels M selected P (fun i => a i ^ (h.val+1))) U w)) =
      g.evaluate hg (spectralLabels M selected P b) U w := by
  change LagrangeRecoveryMachines.recover a (computedInput a b (g.markedCount selected.val) _) = _
  rw [recover_computed_table]
  exact spectral_replacement_from_computed_table g hg selected M U w P a b hzero hcompat

/-- Concrete query semantics and a genuine spectral power resolution imply
correctness of the actual metadata/positive-query/recovery pipeline. -/
theorem preparation_recovery_of_matrix_power_queries [DecidableEq C]
    (g : MixedCode) (hg : g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (P : Fin t → Matrix C C K) (A : Matrix C C K) (a b : Fin t → K)
    (hpowers : ∀ n : ℕ, 0 < n → A ^ n = ∑ i, a i ^ n • P i)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b)
    (transform : ℕ → MixedCode → MixedCode) (answer : MixedCode → K)
    (hquery : ∀ n, 1 ≤ n → answer (transform n g) =
      g.evaluate hg (fun l => if l=selected then A ^ n else M l) U w) :
    recoverContext a ((MatrixFamilyInterpolationMachines.preparation a b selected.val transform g).1,
      (MatrixFamilyInterpolationMachines.preparation a b selected.val transform g).2.map answer) =
      g.evaluate hg (spectralLabels M selected P b) U w := by
  change recoverContext a (metadataFor a b (g.markedCount selected.val),
    (GraphInterpolationQueries.queries transform
      ((ExponentProductTables.representatives a b (g.markedCount selected.val)).length,g)).map answer) = _
  rw [PreparedRecoveryCorrectness.query_answers_ofFn]
  have he : (fun h : Fin (ExponentProductTables.representatives a b (g.markedCount selected.val)).length =>
      answer (transform (h.val+1) g)) =
      (fun h => g.evaluate hg (fun l => if l=selected then A ^ (h.val+1) else M l) U w) := by
    funext h
    exact hquery (h.val+1) (by omega)
  rw [he]
  change LagrangeRecoveryMachines.recover a (computedInput a b (g.markedCount selected.val) _) = _
  rw [recover_computed_table]
  exact spectral_matrix_power_recovery g hg selected M U w P A a b hpowers hzero hcompat

end PlanarHom.PreparedSpectralRecovery
