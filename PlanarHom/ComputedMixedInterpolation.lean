import PlanarHom.ProductRepresentativeSemantics
import PlanarHom.SelectedProductClassSemantics
import PlanarHom.MixedInterpolationRecovery

/-! Exact mixed replacement identities using the actual computed representative table. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
open ProductCompatibility ExponentProductSemantics ExponentProductTables LagrangeRecovery
variable {K : Type} [Field K] [DecidableEq K] {q binaryTypes unaryTypes : ℕ}

/-- The actual table determines all product classes of actual nonzero binary assignments. -/
theorem binary_computed_classes (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (hcompat : Compatible (fun p : Fin q × Fin q => M selected p.1 p.2)
      (fun p : Fin q × Fin q => M' selected p.1 p.2)) :
    ∃ classOf : {σ : Fin g.vertices → Fin q // selectedBinaryProduct g selected.val M σ ≠ 0} →
        Fin (representatives (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
          (g.markedCount selected.val)).length,
      (∀ σ, sourceNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
        (g.markedCount selected.val) (classOf σ) = selectedBinaryProduct g selected.val M σ.val) ∧
      (∀ σ, targetNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
        (g.markedCount selected.val) (classOf σ) = selectedBinaryProduct g selected.val M' σ.val) := by
  have h (σ : {σ : Fin g.vertices → Fin q // selectedBinaryProduct g selected.val M σ ≠ 0}) :
      ∃ i, sourceNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
        (g.markedCount selected.val) i = selectedBinaryProduct g selected.val M σ.val ∧
        targetNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
          (g.markedCount selected.val) i = selectedBinaryProduct g selected.val M' σ.val := by
    obtain ⟨i, hi, ht⟩ := exists_node_for_weak (binaryAlphabet (M selected))
      (binaryAlphabet (M' selected)) (hcompat.comp finProdFinEquiv.symm)
      (WordFrequencies.frequencies (selectedBinaryWord g hg selected σ.val))
      (selectedBinaryWord_frequencies_mem g hg selected σ.val)
      (by rw [← selectedBinaryProduct_eq_exponent_value g hg selected M σ.val]; exact σ.property)
    exact ⟨i, hi.trans (selectedBinaryProduct_eq_exponent_value g hg selected M σ.val).symm,
      ht.trans (selectedBinaryProduct_eq_exponent_value g hg selected M' σ.val).symm⟩
  choose classOf hs ht using h
  exact ⟨classOf, hs, ht⟩

/-- All abstract class invariants are discharged by the table actually computed by FP machines. -/
theorem binary_replacement_from_computed_table (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = M l)
    (hzero : ∀ l i j, l.val = selected.val → M l i j = 0 → M' l i j = 0)
    (hcompat : Compatible (fun p : Fin q × Fin q => M selected p.1 p.2)
      (fun p : Fin q × Fin q => M' selected p.1 p.2)) :
    evaluateReplacement
      (sourceNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) (g.markedCount selected.val))
      (targetNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) (g.markedCount selected.val))
      (fun h => (g.parallelLabel selected.val (h.val + 1)).evaluate
        (parallelLabel_valid selected.val (h.val + 1) binaryTypes unaryTypes g hg) M U w) =
      g.evaluate hg M' U w := by
  obtain ⟨classOf, hs, ht⟩ := binary_computed_classes g hg selected M M' hcompat
  exact binary_replacement_recovered g hg selected.val M M' U w hunchanged hzero classOf _ _
    (sourceNode_injective _ _ _) (sourceNode_nonzero _ _ _) hs ht

/-- The actual unary representative table supplies the same complete class invariants. -/
theorem unary_computed_classes (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (U U' : Fin unaryTypes → Fin q → K)
    (hcompat : Compatible (U selected) (U' selected)) :
    ∃ classOf : {σ : Fin g.vertices → Fin q // selectedUnaryProduct g selected.val U σ ≠ 0} →
        Fin (representatives (U selected) (U' selected) (g.unaryMarkedCount selected.val)).length,
      (∀ σ, sourceNode (U selected) (U' selected) (g.unaryMarkedCount selected.val) (classOf σ) =
        selectedUnaryProduct g selected.val U σ.val) ∧
      (∀ σ, targetNode (U selected) (U' selected) (g.unaryMarkedCount selected.val) (classOf σ) =
        selectedUnaryProduct g selected.val U' σ.val) := by
  have h (σ : {σ : Fin g.vertices → Fin q // selectedUnaryProduct g selected.val U σ ≠ 0}) :
      ∃ i, sourceNode (U selected) (U' selected) (g.unaryMarkedCount selected.val) i =
        selectedUnaryProduct g selected.val U σ.val ∧
        targetNode (U selected) (U' selected) (g.unaryMarkedCount selected.val) i =
          selectedUnaryProduct g selected.val U' σ.val := by
    obtain ⟨i, hi, ht⟩ := exists_node_for_weak (U selected) (U' selected) hcompat
      (WordFrequencies.frequencies (selectedUnaryColors g hg selected σ.val))
      (selectedUnaryColors_frequencies_mem g hg selected σ.val)
      (by rw [← selectedUnaryProduct_eq_exponent_value g hg selected U σ.val]; exact σ.property)
    exact ⟨i, hi.trans (selectedUnaryProduct_eq_exponent_value g hg selected U σ.val).symm,
      ht.trans (selectedUnaryProduct_eq_exponent_value g hg selected U' σ.val).symm⟩
  choose classOf hs ht using h
  exact ⟨classOf, hs, ht⟩

theorem unary_replacement_from_computed_table (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (M : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U U' : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → U' l = U l)
    (hzero : ∀ l i, l.val = selected.val → U l i = 0 → U' l i = 0)
    (hcompat : Compatible (U selected) (U' selected)) :
    evaluateReplacement
      (sourceNode (U selected) (U' selected) (g.unaryMarkedCount selected.val))
      (targetNode (U selected) (U' selected) (g.unaryMarkedCount selected.val))
      (fun h => (g.parallelUnaryLabel selected.val (h.val + 1)).evaluate
        (parallelUnaryLabel_valid selected.val (h.val + 1) g hg) M U w) =
      g.evaluate hg M U' w := by
  obtain ⟨classOf, hs, ht⟩ := unary_computed_classes g hg selected U U' hcompat
  exact unary_replacement_recovered g hg selected.val M U U' w hunchanged hzero classOf _ _
    (sourceNode_injective _ _ _) (sourceNode_nonzero _ _ _) hs ht

end PlanarHom.Complexity.MixedCode
