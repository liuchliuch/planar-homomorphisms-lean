import PlanarHom.ComputedMixedInterpolation
import PlanarHom.MaterializedLagrangeRecoveryMachines

/-!
# Interpolation compatibility at exactly the input's marked length

Lemma 3.10 chooses its source matrix separately for each input length. These
identities require collision consistency only at that length, rather than the
all-length product-map premise of Lemma 3.1. The actual retained list and total
recovery machine are unchanged.
-/
noncomputable section
namespace PlanarHom.ExponentProductTables
open ExponentProductSemantics
variable {K : Type} [Field K] [DecidableEq K] {t : ℕ}

/-- Only collisions in the finite table for this factor count matter. -/
def CompatibleAt (A B : Fin t → K) (m : ℕ) : Prop :=
  ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
    value A xs ≠ 0 → value A xs = value A ys → value B xs = value B ys

omit [DecidableEq K] in
theorem targets_consistent_at (A B : Fin t → K) (m : ℕ) (h : CompatibleAt A B m)
    (p q : K × K) (hp : p ∈ products A B m) (hq : q ∈ products A B m)
    (hz : p.1 ≠ 0) (he : p.1 = q.1) : p.2 = q.2 := by
  rw [products_list_form] at hp hq
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hp
  obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hq
  exact h xs hxs ys hys hz he

/-- Stable source-key dedup retains the correct target under length-local consistency. -/
theorem exists_node_for_weak_at (A B : Fin t → K) {m : ℕ} (h : CompatibleAt A B m)
    (xs : List ℕ) (hxs : xs ∈ ExponentVectors.weak t m) (hz : value A xs ≠ 0) :
    ∃ i : Fin (representatives A B m).length,
      sourceNode A B m i = value A xs ∧ targetNode A B m i = value B xs := by
  let p : K × K := (value A xs, value B xs)
  have hp : p ∈ products A B m := by
    rw [products_list_form]
    exact List.mem_map.mpr ⟨xs, hxs, rfl⟩
  obtain ⟨q, hq, he⟩ := representatives_coverage A B m p hp hz
  have ht := targets_consistent_at A B m h p q hp
    ((representatives_sublist A B m).subset hq) hz he
  obtain ⟨i, hi⟩ := List.get_of_mem hq
  refine ⟨i, ?_, ?_⟩
  · change ((representatives A B m).get i).1 = value A xs
    rw [hi]
    exact he.symm
  · change ((representatives A B m).get i).2 = value B xs
    rw [hi]
    exact ht.symm

omit [DecidableEq K] in
theorem compatibleAt_of_compatible (A B : Fin t → K)
    (h : ProductCompatibility.Compatible A B) (m : ℕ) : CompatibleAt A B m :=
  fun xs hxs ys hys hz he => target_eq_of_weak_collision A B h xs ys hxs hys hz he

end PlanarHom.ExponentProductTables

namespace PlanarHom.Complexity.MixedCode
open ExponentProductTables ExponentProductSemantics LagrangeRecovery
variable {K : Type} [Field K] [DecidableEq K] {q binaryTypes unaryTypes : ℕ}

/-- The actual table supplies all binary assignment classes from length-local data. -/
theorem binary_computed_classes_at (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (hcompat : CompatibleAt (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
      (g.markedCount selected.val)) :
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
    obtain ⟨i, hi, ht⟩ := exists_node_for_weak_at (binaryAlphabet (M selected))
      (binaryAlphabet (M' selected)) hcompat
      (WordFrequencies.frequencies (selectedBinaryWord g hg selected σ.val))
      (selectedBinaryWord_frequencies_mem g hg selected σ.val)
      (by rw [← selectedBinaryProduct_eq_exponent_value g hg selected M σ.val]; exact σ.property)
    exact ⟨i, hi.trans (selectedBinaryProduct_eq_exponent_value g hg selected M σ.val).symm,
      ht.trans (selectedBinaryProduct_eq_exponent_value g hg selected M' σ.val).symm⟩
  choose classOf hs ht using h
  exact ⟨classOf, hs, ht⟩

/-- Source (3.7) is sufficient for the genuine matrix-replacement identity. -/
theorem binary_replacement_from_computed_table_at (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = M l)
    (hzero : ∀ l i j, l.val = selected.val → M l i j = 0 → M' l i j = 0)
    (hcompat : CompatibleAt (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
      (g.markedCount selected.val)) :
    evaluateReplacement
      (sourceNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) (g.markedCount selected.val))
      (targetNode (binaryAlphabet (M selected)) (binaryAlphabet (M' selected)) (g.markedCount selected.val))
      (fun h => (g.parallelLabel selected.val (h.val + 1)).evaluate
        (parallelLabel_valid selected.val (h.val + 1) binaryTypes unaryTypes g hg) M U w) =
      g.evaluate hg M' U w := by
  obtain ⟨classOf, hs, ht⟩ := binary_computed_classes_at g hg selected M M' hcompat
  exact binary_replacement_recovered g hg selected.val M M' U w hunchanged hzero classOf _ _
    (sourceNode_injective _ _ _) (sourceNode_nonzero _ _ _) hs ht

/-- The total materialized recovery program evaluates exactly the replacement
using only the current input length's consistency hypothesis. -/
theorem materialized_binary_recovery_at (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (selected : Fin binaryTypes)
    (M M' : Fin binaryTypes → Matrix (Fin q) (Fin q) K)
    (U : Fin unaryTypes → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = M l)
    (hzero : ∀ l i j, l.val = selected.val → M l i j = 0 → M' l i j = 0)
    (hcompat : CompatibleAt (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
      (g.markedCount selected.val)) :
    MaterializedLagrangeRecoveryMachines.recover
      (representatives (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
        (g.markedCount selected.val),
       List.ofFn (fun h : Fin (representatives (binaryAlphabet (M selected))
         (binaryAlphabet (M' selected)) (g.markedCount selected.val)).length =>
         (g.parallelLabel selected.val (h.val + 1)).evaluate
        (parallelLabel_valid selected.val (h.val + 1) binaryTypes unaryTypes g hg) M U w)) =
      g.evaluate hg M' U w := by
  rw [MaterializedLagrangeRecoveryMachines.recover_computed_table]
  exact binary_replacement_from_computed_table_at g hg selected M M' U w hunchanged hzero hcompat

end PlanarHom.Complexity.MixedCode
