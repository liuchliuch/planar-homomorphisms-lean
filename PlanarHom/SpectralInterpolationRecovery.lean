import PlanarHom.SpectralInterpolationSemantics
import PlanarHom.ProductRepresentativeSemantics
import PlanarHom.ProductClassRecovery

/-!
# Computed-table recovery for spectral interpolation

The finite expansion is grouped by the actual source scalar products. The
frequency lists belong to the implemented weak-composition table, numerical
collisions are merged by the existing representative algorithm, and its genuine
shifted Lagrange coefficients recover the target. Neither recovery nor a
computable product-class map is a hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open ProductCompatibility ExponentProductSemantics ExponentProductTables LagrangeRecovery
variable {C K : Type} [Fintype C] [Field K] [DecidableEq K] {binaryTypes unaryTypes t m : ℕ}

/-- Actual projector tuples give actual weak-composition frequency lists. -/
theorem spectral_frequencies_mem (choice : Fin m → Fin t) :
    WordFrequencies.frequencies (List.ofFn choice) ∈ ExponentVectors.weak t m := by
  simpa only [List.length_ofFn] using WordFrequencies.frequencies_mem_weak (List.ofFn choice)

/-- The scalar product of a tuple agrees with the implemented exponent product. -/
theorem spectralProduct_eq_value (a : Fin t → K) (choice : Fin m → Fin t) :
    spectralProduct a choice = value a (WordFrequencies.frequencies (List.ofFn choice)) := by
  rw [value_frequencies]
  simp only [List.map_ofFn, List.prod_ofFn, spectralProduct, Function.comp_apply]

/-- The source collision condition selects a genuine retained table row with
both the source and target tuple products. -/
theorem spectral_computed_classes (a b : Fin t → K) (hcompat : Compatible a b) (m : ℕ) :
    ∃ classOf : {choice : Fin m → Fin t // spectralProduct a choice ≠ 0} →
        Fin (representatives a b m).length,
      (∀ choice, sourceNode a b m (classOf choice) = spectralProduct a choice.val) ∧
      (∀ choice, targetNode a b m (classOf choice) = spectralProduct b choice.val) := by
  have h (choice : {choice : Fin m → Fin t // spectralProduct a choice ≠ 0}) :
      ∃ i, sourceNode a b m i = spectralProduct a choice.val ∧
        targetNode a b m i = spectralProduct b choice.val := by
    obtain ⟨i, hs, ht⟩ := exists_node_for_weak a b hcompat
      (WordFrequencies.frequencies (List.ofFn choice.val)) (spectral_frequencies_mem choice.val)
      (by rw [← spectralProduct_eq_value]; exact choice.property)
    exact ⟨i, hs.trans (spectralProduct_eq_value a choice.val).symm,
      ht.trans (spectralProduct_eq_value b choice.val).symm⟩
  choose classOf hs ht using h
  exact ⟨classOf, hs, ht⟩

/-- Source-zero tuples vanish in the target whenever zero eigenvalues remain zero. -/
theorem spectralProduct_zero (a b : Fin t → K) (hzero : ∀ i, a i = 0 → b i = 0)
    (choice : Fin m → Fin t) (hz : spectralProduct a choice = 0) :
    spectralProduct b choice = 0 := by
  obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp hz
  exact Finset.prod_eq_zero hi (hzero (choice i) hz)

/-- Exact recovery of the selected spectral replacement from the implemented
source/target representative table. Empty selected sets and zero eigenvalues
are included without special oracle assumptions. -/
theorem spectral_replacement_from_computed_table
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) (P : Fin t → Matrix C C K)
    (a b : Fin t → K) (hzero : ∀ i, a i = 0 → b i = 0) (hcompat : Compatible a b) :
    evaluateReplacement (sourceNode a b (g.markedCount selected.val))
      (targetNode a b (g.markedCount selected.val))
      (fun h => g.evaluate hg (spectralLabels M selected P (fun i => a i ^ (h.val + 1))) U w) =
      g.evaluate hg (spectralLabels M selected P b) U w := by
  classical
  obtain ⟨classOf, hs, ht⟩ := spectral_computed_classes a b hcompat (g.markedCount selected.val)
  simp_rw [evaluate_spectral_powers, evaluate_spectral_expansion]
  apply evaluateReplacement_nonzero_classes
    (fun z : (Fin g.vertices → C) × (Fin (g.markedCount selected.val) → Fin t) => spectralProduct a z.2)
    (fun z => spectralProduct b z.2) (spectralRest g hg selected M U w P)
    (fun z hz => spectralProduct_zero a b hzero z.2 hz)
    (fun z => classOf ⟨z.val.2, z.property⟩) _ _
    (sourceNode_injective a b _) (sourceNode_nonzero a b _)
    (fun z => hs ⟨z.val.2, z.property⟩) (fun z => ht ⟨z.val.2, z.property⟩)

/-- Specialization to genuine powers of one source matrix. The only matrix
hypothesis is its spectral power formula, separately supplied by the spectral
theorem; the finite partition expansion and recovery are proved above. -/
theorem spectral_matrix_power_recovery [DecidableEq C]
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) (P : Fin t → Matrix C C K)
    (A : Matrix C C K) (a b : Fin t → K)
    (hpowers : ∀ h : ℕ, 0 < h → A ^ h = ∑ i, a i ^ h • P i)
    (hzero : ∀ i, a i = 0 → b i = 0) (hcompat : Compatible a b) :
    evaluateReplacement (sourceNode a b (g.markedCount selected.val))
      (targetNode a b (g.markedCount selected.val))
      (fun h => g.evaluate hg (fun l => if l = selected then A ^ (h.val + 1) else M l) U w) =
      g.evaluate hg (spectralLabels M selected P b) U w := by
  have hp : (fun h : Fin (representatives a b (g.markedCount selected.val)).length =>
      g.evaluate hg (fun l => if l = selected then A ^ (h.val + 1) else M l) U w) =
      (fun h => g.evaluate hg (spectralLabels M selected P (fun i => a i ^ (h.val + 1))) U w) := by
    funext h
    rw [hpowers (h.val + 1) (Nat.succ_pos _)]
    rfl
  rw [hp]
  exact spectral_replacement_from_computed_table g hg selected M U w P a b hzero hcompat

end PlanarHom.Complexity.MixedCode
