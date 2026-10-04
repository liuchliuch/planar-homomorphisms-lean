import PlanarHom.DependentMatrixFamilyPreparation
import PlanarHom.DependentTargetRecoverySemantics
import PlanarHom.CrossFieldMixedRecovery
import PlanarHom.PreparedRecoveryCorrectness

/-! Exact source-only queries and heterogeneous target recovery for the computed preparation. -/
noncomputable section
namespace PlanarHom.DependentMatrixFamilyRecovery
open Complexity Complexity.MixedCode FiniteLanguageAliases DependentMatrixFamilyPreparation
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
variable (inclusion : ∀ x, L →+* K x) {q bt ut : ℕ}

private theorem appendOne_unchanged (x : X) (M : Fin bt → Matrix (Fin q) (Fin q) L)
    (A : Matrix (Fin q) (Fin q) L) (B : Matrix (Fin q) (Fin q) (K x))
    (l : Fin (bt+1)) (hl : l.val ≠ bt) :
    appendOne (fun l i j => inclusion x (M l i j)) B l =
      fun i j => inclusion x (appendOne M A l i j) := by
  revert hl
  refine Fin.addCases (fun j _ => ?_) (fun j h => ?_) l
  · rw [appendOne_old,appendOne_old]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp at h

 theorem preparation_recovery_correct
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x))
    (n₀ : ℕ) (candidates : Polynomial ℕ)
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (x : X) (hSample : ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (g : MixedCode) (hg : g.Valid (bt+1) ut) :
    DependentTargetAggregation.recover K inclusion (fun x => binaryAlphabet (B x))
      ((x,g.markedCount bt),
        ((preparation K F B n₀ candidates bt (x,g)).1.2,
         (preparation K F B n₀ candidates bt (x,g)).2.map (DynamicMatrixFamilySource.answer M U w F))) =
      ⟨x,g.evaluate hg (appendOne (fun l i j => inclusion x (M l i j)) (B x))
        (fun l i => inclusion x (U l i)) (fun i => inclusion x (w i))⟩ := by
  let n := sampleIndex K F B n₀ candidates bt (x,g)
  have hs := sample_spec K F B n₀ candidates bt (x,g) (hSample _)
  have hc := CrossFieldMixedRecovery.binary_recovery (inclusion x) g hg (Fin.last bt)
    (appendOne M (F n)) (appendOne (fun l i j => inclusion x (M l i j)) (B x)) U w
    (fun l hl => appendOne_unchanged K inclusion x M (F n) (B x) l hl)
    (by simpa only [appendOne_aux] using hNonzero n hs.1)
    (by simpa only [appendOne_aux] using hs.2.2)
  simp only [appendOne_aux, Fin.val_last] at hc
  change DependentTargetAggregation.recover K inclusion (fun x => binaryAlphabet (B x))
    ((x,g.markedCount bt),(table K F B n₀ candidates bt (x,g),
      ((GraphInterpolationQueries.queries (MixedCode.parallelLabel bt)
        ((table K F B n₀ candidates bt (x,g)).length,g)).map (fun query => (n,query))).map
          (DynamicMatrixFamilySource.answer M U w F))) = _
  rw [List.map_map,PreparedRecoveryCorrectness.query_answers_ofFn]
  have hvals : (fun h : Fin (table K F B n₀ candidates bt (x,g)).length =>
      (DynamicMatrixFamilySource.answer M U w F ∘ (fun query => (n,query)))
        (g.parallelLabel bt (h.val+1))) =
      (fun h => (g.parallelLabel bt (h.val+1)).evaluate
        (parallelLabel_valid bt (h.val+1) (bt+1) ut g hg) (appendOne M (F n)) U w) := by
    funext h
    exact totalEvaluation_valid _ _ _ _ _
  rw [hvals]
  dsimp only [table]
  rw [DependentTargetAggregation.recover_representatives]
  congr 1

end PlanarHom.DependentMatrixFamilyRecovery
