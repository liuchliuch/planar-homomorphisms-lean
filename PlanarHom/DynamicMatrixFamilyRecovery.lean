import PlanarHom.DynamicMatrixFamilyPreparation
import PlanarHom.PreparedRecoveryCorrectness

/-! Exact correctness of the dynamic sample/table/parallel-query recovery program. -/
noncomputable section
namespace PlanarHom.DynamicMatrixFamilyRecovery
open Complexity Complexity.MixedCode FiniteLanguageAliases DynamicMatrixFamilyPreparation
variable {K : Type} [Field K] [DecidableEq K] {q bt ut : ℕ}

omit [Field K] [DecidableEq K] in
theorem appendOne_unchanged (M : Fin bt → Matrix (Fin q) (Fin q) K)
    (A B : Matrix (Fin q) (Fin q) K) (l : Fin (bt+1)) (hl : l.val ≠ bt) :
    appendOne M B l = appendOne M A l := by
  revert hl
  refine Fin.addCases (fun j _ => ?_) (fun j h => ?_) l
  · rw [appendOne_old, appendOne_old]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp at h

/-- No all-length collision premise is used: only the finite test for the
current marked length, and nonzero source entries at the selected sample. -/
theorem preparation_recovery_correct
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (c : Polynomial ℕ)
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B) m)
    (g : MixedCode) (hg : g.Valid (bt+1) ut) :
    MaterializedLagrangeRecoveryMachines.recover
      ((preparation F B n₀ c bt g).1,
       (preparation F B n₀ c bt g).2.map (DynamicMatrixFamilySource.answer M U w F)) =
      g.evaluate hg (appendOne M B) U w := by
  let n := sampleIndex F B n₀ c bt g
  have hs := sample_spec F B n₀ c bt g (hSample _)
  have hc := materialized_binary_recovery_at g hg (Fin.last bt)
    (appendOne M (F n)) (appendOne M B) U w
    (fun l hl => appendOne_unchanged M (F n) B l hl)
    (fun l i j hl hz => by
      have he : l = Fin.last bt := Fin.ext hl
      subst l
      exact False.elim (hNonzero n hs.1 i j (by simpa only [appendOne_aux] using hz)))
    (by simpa only [appendOne_aux] using hs.2.2)
  simp only [appendOne_aux, Fin.val_last] at hc
  change MaterializedLagrangeRecoveryMachines.recover
    (table F B n₀ c bt g,
      ((GraphInterpolationQueries.queries (MixedCode.parallelLabel bt)
        ((table F B n₀ c bt g).length,g)).map (fun query => (n, query))).map
          (DynamicMatrixFamilySource.answer M U w F)) = _
  rw [List.map_map, PreparedRecoveryCorrectness.query_answers_ofFn]
  have hvals : (fun h : Fin (table F B n₀ c bt g).length =>
      (DynamicMatrixFamilySource.answer M U w F ∘ (fun query => (n,query)))
        (g.parallelLabel bt (h.val+1))) =
      (fun h => (g.parallelLabel bt (h.val+1)).evaluate
        (parallelLabel_valid bt (h.val+1) (bt+1) ut g hg) (appendOne M (F n)) U w) := by
    funext h
    exact totalEvaluation_valid _ _ _ _ _
  rw [hvals]
  exact hc

end PlanarHom.DynamicMatrixFamilyRecovery
