import PlanarHom.LagrangeRecoveryListSemantics
import PlanarHom.ComputedMixedInterpolation

/-! The actual recovery subroutine applied to the actual mixed query values. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
open ProductCompatibility ExponentProductTables LagrangeRecoveryMachines LagrangeRecoveryListSemantics
variable {K : Type} [Field K] [DecidableEq K] {q binaryTypes unaryTypes : ℕ}

/-- Exact binary recovery with the source's positive-length product-map hypothesis. -/
theorem binary_recovery_correct (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = M l)
    (hzero : ∀ i j, M selected i j = 0 → M' selected i j = 0)
    (hmaps : HasProductMaps (fun p : Fin q × Fin q => M selected p.1 p.2)
      (fun p : Fin q × Fin q => M' selected p.1 p.2)) :
    recover (binaryAlphabet (M selected))
      (computedInput (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
        (g.markedCount selected.val)
        (List.ofFn (fun h : Fin (representatives (binaryAlphabet (M selected))
          (binaryAlphabet (M' selected)) (g.markedCount selected.val)).length =>
          (g.parallelLabel selected.val (h.val + 1)).evaluate
            (parallelLabel_valid selected.val (h.val + 1) binaryTypes unaryTypes g hg) M U w))) =
      g.evaluate hg M' U w := by
  rw [recover_computed_table]
  apply binary_replacement_from_computed_table g hg selected M M' U w hunchanged
  · intro l i j hl
    have he : l = selected := Fin.ext hl
    simpa only [he] using hzero i j
  · exact compatible_of_hasProductMaps _ _ hmaps

/-- The same actual recovery program proves the unary replacement identity. -/
theorem unary_recovery_correct (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (M : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U U' : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → U' l = U l)
    (hzero : ∀ i, U selected i = 0 → U' selected i = 0)
    (hmaps : HasProductMaps (U selected) (U' selected)) :
    recover (U selected)
      (computedInput (U selected) (U' selected) (g.unaryMarkedCount selected.val)
        (List.ofFn (fun h : Fin (representatives (U selected) (U' selected)
          (g.unaryMarkedCount selected.val)).length =>
          (g.parallelUnaryLabel selected.val (h.val + 1)).evaluate
            (parallelUnaryLabel_valid selected.val (h.val + 1) g hg) M U w))) =
      g.evaluate hg M U' w := by
  rw [recover_computed_table]
  apply unary_replacement_from_computed_table g hg selected M U U' w hunchanged
  · intro l i hl
    have he : l = selected := Fin.ext hl
    simpa only [he] using hzero i
  · exact compatible_of_hasProductMaps _ _ hmaps

end PlanarHom.Complexity.MixedCode
