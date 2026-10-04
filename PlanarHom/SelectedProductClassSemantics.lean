import PlanarHom.SelectedOccurrenceWords
import PlanarHom.ExponentProductSemantics

/-! Exact assignment-to-representative invariants for the computed product-class table. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
open ProductCompatibility ExponentProductSemantics
variable {K : Type} [Field K] {q binaryTypes unaryTypes : ℕ}

/-- Fixed ordering of the q² interaction entries used by the exponent enumerator. -/
def binaryAlphabet (M : Matrix (Fin q) (Fin q) K) (i : Fin (q * q)) : K :=
  M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The actual assignment product occurs in the concrete exponent table. -/
theorem selectedBinaryProduct_eq_exponent_value (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M : Fin binaryTypes → Matrix (Fin q) (Fin q) K) (σ : Fin g.vertices → Fin q) :
    selectedBinaryProduct g selected.val M σ =
      value (binaryAlphabet (M selected))
        (WordFrequencies.frequencies (selectedBinaryWord g hg selected σ)) := by
  rw [value_frequencies]
  simpa only [selectedBinaryWord, List.map_map, Function.comp_def, binaryAlphabet,
    Equiv.symm_apply_apply] using (selectedBinaryColors_product g hg selected M σ).symm

/-- Any retained nonzero representative with the same numerical source product
has the required target product. No computable θ map is assumed. -/
theorem binary_target_of_representative (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (hcompat : Compatible (fun p : Fin q × Fin q => M selected p.1 p.2)
      (fun p : Fin q × Fin q => M' selected p.1 p.2))
    (σ : Fin g.vertices → Fin q) (xs : List ℕ)
    (hxs : xs ∈ ExponentVectors.weak (q * q) (g.markedCount selected.val))
    (hnz : selectedBinaryProduct g selected.val M σ ≠ 0)
    (hsource : value (binaryAlphabet (M selected)) xs = selectedBinaryProduct g selected.val M σ) :
    value (binaryAlphabet (M' selected)) xs = selectedBinaryProduct g selected.val M' σ := by
  rw [selectedBinaryProduct_eq_exponent_value g hg selected M' σ]
  apply target_eq_of_weak_collision _ _ (hcompat.comp finProdFinEquiv.symm) xs _ hxs
    (selectedBinaryWord_frequencies_mem g hg selected σ)
  · exact hsource ▸ hnz
  · exact hsource.trans (selectedBinaryProduct_eq_exponent_value g hg selected M σ)

/-- The exact unary assignment product is the product of its q-coordinate frequency vector. -/
theorem selectedUnaryProduct_eq_exponent_value (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin unaryTypes)
    (U : Fin unaryTypes → Fin q → K) (σ : Fin g.vertices → Fin q) :
    selectedUnaryProduct g selected.val U σ = value (U selected)
      (WordFrequencies.frequencies (selectedUnaryColors g hg selected σ)) := by
  rw [value_frequencies]
  exact (selectedUnaryColors_product g hg selected U σ).symm

theorem unary_target_of_representative (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin unaryTypes)
    (U U' : Fin unaryTypes → Fin q → K) (hcompat : Compatible (U selected) (U' selected))
    (σ : Fin g.vertices → Fin q) (xs : List ℕ)
    (hxs : xs ∈ ExponentVectors.weak q (g.unaries.filter (fun e => e.2 = selected.val)).length)
    (hnz : selectedUnaryProduct g selected.val U σ ≠ 0)
    (hsource : value (U selected) xs = selectedUnaryProduct g selected.val U σ) :
    value (U' selected) xs = selectedUnaryProduct g selected.val U' σ := by
  rw [selectedUnaryProduct_eq_exponent_value g hg selected U' σ]
  apply target_eq_of_weak_collision _ _ hcompat xs _ hxs
    (selectedUnaryColors_frequencies_mem g hg selected σ)
  · exact hsource ▸ hnz
  · exact hsource.trans (selectedUnaryProduct_eq_exponent_value g hg selected U σ)

end PlanarHom.Complexity.MixedCode
