import PlanarHom.MixedProductSemantics
import PlanarHom.MixedPlanarCode
import Mathlib.Algebra.BigOperators.Ring.List

/-! Zero-preserving replacements and unconditional planarity of unary replication. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
variable {C K : Type} [Field K] {binaryTypes unaryTypes : ℕ}

/-- A source-zero assignment remains zero after any selected zero-preserving replacement. -/
theorem selectedBinaryProduct_zero_of_zero (g : MixedCode) (selected : ℕ)
    (M M' : Fin binaryTypes → Matrix C C K)
    (hzero : ∀ l i j, l.val = selected → M l i j = 0 → M' l i j = 0)
    (σ : Fin g.vertices → C) (hz : selectedBinaryProduct g selected M σ = 0) :
    selectedBinaryProduct g selected M' σ = 0 := by
  unfold selectedBinaryProduct at hz ⊢
  apply List.prod_eq_zero_iff.mpr
  obtain ⟨e, he, hez⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hz)
  refine List.mem_map.mpr ⟨e, he, ?_⟩
  have hsel := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at hsel
  unfold binaryValue at hez ⊢
  split at hez
  · rename_i hv
    rw [dif_pos hv]
    exact hzero _ _ _ hsel hez
  · exact False.elim (one_ne_zero hez)

/-- The same zero-preservation argument applies to unary occurrences. -/
theorem selectedUnaryProduct_zero_of_zero (g : MixedCode) (selected : ℕ)
    (U U' : Fin unaryTypes → C → K)
    (hzero : ∀ l i, l.val = selected → U l i = 0 → U' l i = 0)
    (σ : Fin g.vertices → C) (hz : selectedUnaryProduct g selected U σ = 0) :
    selectedUnaryProduct g selected U' σ = 0 := by
  unfold selectedUnaryProduct at hz ⊢
  apply List.prod_eq_zero_iff.mpr
  obtain ⟨e, he, hez⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hz)
  refine List.mem_map.mpr ⟨e, he, ?_⟩
  have hsel := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at hsel
  unfold unaryValue at hez ⊢
  split at hez
  · rename_i hv
    rw [dif_pos hv]
    exact hzero _ _ hsel hez
  · exact False.elim (one_ne_zero hez)

@[simp] theorem parallelUnaryLabel_underlying (selected s : ℕ) (g : MixedCode) :
    (g.parallelUnaryLabel selected s).underlying = g.underlying := rfl

/-- Unary copies do not change the actual ordinary incidence graph, so no ribbon is needed. -/
theorem PlanarValid.parallelUnaryLabel {g : MixedCode}
    (hg : g.PlanarValid binaryTypes unaryTypes) (selected s : ℕ) :
    (g.parallelUnaryLabel selected s).PlanarValid binaryTypes unaryTypes :=
  ⟨parallelUnaryLabel_valid selected s g hg.1, hg.2⟩

end PlanarHom.Complexity.MixedCode
