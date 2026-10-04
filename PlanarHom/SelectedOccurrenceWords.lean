import PlanarHom.MixedProductSemantics
import PlanarHom.MarkedOccurrenceCount
import PlanarHom.UnaryOccurrenceCount
import PlanarHom.WordFrequencies

/-! Actual selected-entry words and their frequency-vector representation. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
open scoped BigOperators
variable {C K : Type} {binaryTypes unaryTypes : ℕ}

/-- Ordered endpoint color pairs of every selected occurrence, including repeated loops. -/
def selectedBinaryColors (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (σ : Fin g.vertices → C) : List (C × C) :=
  (g.edges.filter (fun e => e.2.2 = selected.val)).attach.map (fun e =>
    let hv := hg.1 e.val (List.mem_filter.mp e.property).1
    (σ ⟨e.val.1, hv.1⟩, σ ⟨e.val.2.1, hv.2.1⟩))

@[simp] theorem selectedBinaryColors_length (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (σ : Fin g.vertices → C) :
    (selectedBinaryColors g hg selected σ).length = g.markedCount selected.val := by
  simp [selectedBinaryColors, markedCount]

/-- The actual selected product is exactly the matrix-entry product on that word. -/
theorem selectedBinaryColors_product [CommSemiring K] (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M : Fin binaryTypes → Matrix C C K) (σ : Fin g.vertices → C) :
    ((selectedBinaryColors g hg selected σ).map (fun p => M selected p.1 p.2)).prod =
      selectedBinaryProduct g selected.val M σ := by
  unfold selectedBinaryColors selectedBinaryProduct
  rw [List.map_map]
  apply congrArg List.prod
  trans (g.edges.filter (fun e => e.2.2 = selected.val)).attach.map
    (fun e => binaryValue g.vertices binaryTypes M σ e.val)
  · apply List.map_congr_left
    intro e _
    have hv := hg.1 e.val (List.mem_filter.mp e.property).1
    have he : e.val.2.2 = selected.val := by simpa using (List.mem_filter.mp e.property).2
    have hlabel : (⟨e.val.2.2, hv.2.2⟩ : Fin binaryTypes) = selected := Fin.ext he
    simp only [Function.comp_apply, binaryValue, dif_pos hv, hlabel]
  · exact List.attach_map_val

/-- The selected unary word retains every listed occurrence. -/
def selectedUnaryColors (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (σ : Fin g.vertices → C) : List C :=
  (g.unaries.filter (fun e => e.2 = selected.val)).attach.map (fun e =>
    σ ⟨e.val.1, (hg.2 e.val (List.mem_filter.mp e.property).1).1⟩)

theorem selectedUnaryColors_length (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin unaryTypes) (σ : Fin g.vertices → C) :
    (selectedUnaryColors g hg selected σ).length =
      (g.unaries.filter (fun e => e.2 = selected.val)).length := by
  simp [selectedUnaryColors]

theorem selectedUnaryColors_product [CommSemiring K] (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin unaryTypes)
    (U : Fin unaryTypes → C → K) (σ : Fin g.vertices → C) :
    ((selectedUnaryColors g hg selected σ).map (U selected)).prod =
      selectedUnaryProduct g selected.val U σ := by
  unfold selectedUnaryColors selectedUnaryProduct
  rw [List.map_map]
  apply congrArg List.prod
  trans (g.unaries.filter (fun e => e.2 = selected.val)).attach.map
    (fun e => unaryValue g.vertices unaryTypes U σ e.val)
  · apply List.map_congr_left
    intro e _
    have hv := hg.2 e.val (List.mem_filter.mp e.property).1
    have he : e.val.2 = selected.val := by simpa using (List.mem_filter.mp e.property).2
    have hlabel : (⟨e.val.2, hv.2⟩ : Fin unaryTypes) = selected := Fin.ext he
    simp only [Function.comp_apply, unaryValue, dif_pos hv, hlabel]
  · exact List.attach_map_val

/-- Binary positions use the fixed q² alphabet in the standard Fin product order. -/
def selectedBinaryWord {q : ℕ} (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (σ : Fin g.vertices → Fin q) : List (Fin (q * q)) :=
  (selectedBinaryColors g hg selected σ).map finProdFinEquiv

@[simp] theorem selectedBinaryWord_length {q : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes) (σ : Fin g.vertices → Fin q) :
    (selectedBinaryWord g hg selected σ).length = g.markedCount selected.val := by
  simp [selectedBinaryWord]

/-- Every actual assignment gives a vector in the compiled weak-composition enumeration. -/
theorem selectedBinaryWord_frequencies_mem {q : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes) (σ : Fin g.vertices → Fin q) :
    WordFrequencies.frequencies (selectedBinaryWord g hg selected σ) ∈
      ExponentVectors.weak (q * q) (g.markedCount selected.val) := by
  simpa only [selectedBinaryWord_length] using
    WordFrequencies.frequencies_mem_weak (selectedBinaryWord g hg selected σ)

/-- Source and target matrices obey the same exact frequency-product identity. -/
theorem selectedBinaryProduct_eq_frequencies {q : ℕ} [CommSemiring K] (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M : Fin binaryTypes → Matrix (Fin q) (Fin q) K) (σ : Fin g.vertices → Fin q) :
    selectedBinaryProduct g selected.val M σ =
      ∏ i : Fin (q * q), M selected (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 ^
        (selectedBinaryWord g hg selected σ).count i := by
  rw [← WordFrequencies.product_eq_frequencies]
  simp only [selectedBinaryWord, List.map_map, Function.comp_def, Equiv.symm_apply_apply]
  exact (selectedBinaryColors_product g hg selected M σ).symm

/-- Unary selected assignments use the q-letter weak-composition enumeration. -/
theorem selectedUnaryColors_frequencies_mem {q : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin unaryTypes) (σ : Fin g.vertices → Fin q) :
    WordFrequencies.frequencies (selectedUnaryColors g hg selected σ) ∈
      ExponentVectors.weak q (g.unaries.filter (fun e => e.2 = selected.val)).length := by
  simpa only [selectedUnaryColors_length] using
    WordFrequencies.frequencies_mem_weak (selectedUnaryColors g hg selected σ)

theorem selectedUnaryProduct_eq_frequencies {q : ℕ} [CommSemiring K] (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin unaryTypes)
    (U : Fin unaryTypes → Fin q → K) (σ : Fin g.vertices → Fin q) :
    selectedUnaryProduct g selected.val U σ =
      ∏ i : Fin q, U selected i ^ (selectedUnaryColors g hg selected σ).count i := by
  rw [← WordFrequencies.product_eq_frequencies]
  exact (selectedUnaryColors_product g hg selected U σ).symm

end PlanarHom.Complexity.MixedCode
