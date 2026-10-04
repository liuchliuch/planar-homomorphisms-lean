import PlanarHom.ComputedRecoveryCorrectness
import PlanarHom.ProductInterpolationPreparationMachines
import PlanarHom.MixedTotalEvaluation

/-! Direct postprocess correctness for the actual nonadaptive preparation and answer list. -/

noncomputable section
namespace PlanarHom.PreparedRecoveryCorrectness
open Complexity Complexity.MixedCode ProductInterpolationPreparationMachines
open ProductCompatibility LagrangeRecoveryMachines LagrangeRecoveryListSemantics

/-- The query generator's actual ascending range matches the interpolation vector order. -/
theorem query_answers_ofFn {T : Type} (transform : ℕ → MixedCode → MixedCode)
    (n : ℕ) (g : MixedCode) (f : MixedCode → T) :
    (GraphInterpolationQueries.queries transform (n,g)).map f =
      List.ofFn (fun h : Fin n => f (transform (h.val + 1) g)) := by
  apply List.ext_getElem (by simp [GraphInterpolationQueries.queries])
  intro i hi hj
  simp only [GraphInterpolationQueries.queries, List.getElem_map, List.getElem_range,
    List.getElem_ofFn]

variable {K : Type} [Field K] [DecidableEq K] {q binaryTypes unaryTypes : ℕ}

/-- The complete actual binary preprocessor, source-value list and postprocessor
compose to the target mixed value, with all table/class/order invariants derived. -/
theorem binary_preparation_recovery_correct (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = M l)
    (hzero : ∀ i j, M selected i j = 0 → M' selected i j = 0)
    (hcompat : Compatible (fun p : Fin q × Fin q => M selected p.1 p.2)
      (fun p : Fin q × Fin q => M' selected p.1 p.2)) :
    recoverContext (binaryAlphabet (M selected))
      ((binaryPreparation (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) selected.val g).1,
        ((binaryPreparation (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) selected.val g).2.map
          (totalEvaluation M U w))) = g.evaluate hg M' U w := by
  change recover (binaryAlphabet (M selected))
    (computedInput (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) (g.markedCount selected.val)
      ((GraphInterpolationQueries.queries (parallelLabel selected.val)
        ((ExponentProductTables.representatives (binaryAlphabet (M selected))
          (binaryAlphabet (M' selected)) (g.markedCount selected.val)).length,g)).map
            (totalEvaluation M U w))) = _
  rw [query_answers_ofFn]
  have hvals : (fun h : Fin (ExponentProductTables.representatives (binaryAlphabet (M selected))
      (binaryAlphabet (M' selected)) (g.markedCount selected.val)).length =>
      totalEvaluation M U w (g.parallelLabel selected.val (h.val + 1))) =
      (fun h => (g.parallelLabel selected.val (h.val + 1)).evaluate
        (parallelLabel_valid selected.val (h.val + 1) binaryTypes unaryTypes g hg) M U w) := by
    funext h
    exact totalEvaluation_valid M U w _ _
  rw [hvals]
  exact binary_recovery_correct g hg selected M M' U w hunchanged hzero
    (hasProductMaps_of_compatible _ _ hcompat)

/-- Unary-label analogue, including preserved binary companions and all source-zero assignments. -/
theorem unary_preparation_recovery_correct (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (M : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U U' : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → U' l = U l)
    (hzero : ∀ i, U selected i = 0 → U' selected i = 0)
    (hcompat : Compatible (U selected) (U' selected)) :
    recoverContext (U selected)
      ((unaryPreparation (U selected) (U' selected) selected.val g).1,
        ((unaryPreparation (U selected) (U' selected) selected.val g).2.map (totalEvaluation M U w))) =
      g.evaluate hg M U' w := by
  change recover (U selected)
    (computedInput (U selected) (U' selected) (g.unaryMarkedCount selected.val)
      ((GraphInterpolationQueries.queries (parallelUnaryLabel selected.val)
        ((ExponentProductTables.representatives (U selected) (U' selected)
          (g.unaryMarkedCount selected.val)).length,g)).map (totalEvaluation M U w))) = _
  rw [query_answers_ofFn]
  have hvals : (fun h : Fin (ExponentProductTables.representatives (U selected) (U' selected)
      (g.unaryMarkedCount selected.val)).length =>
      totalEvaluation M U w (g.parallelUnaryLabel selected.val (h.val + 1))) =
      (fun h => (g.parallelUnaryLabel selected.val (h.val + 1)).evaluate
        (parallelUnaryLabel_valid selected.val (h.val + 1) g hg) M U w) := by
    funext h
    exact totalEvaluation_valid M U w _ _
  rw [hvals]
  exact unary_recovery_correct g hg selected M U U' w hunchanged hzero
    (hasProductMaps_of_compatible _ _ hcompat)

end PlanarHom.PreparedRecoveryCorrectness
