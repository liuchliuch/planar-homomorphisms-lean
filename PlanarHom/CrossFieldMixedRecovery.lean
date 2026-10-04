import PlanarHom.CrossFieldProductClasses

/-! Complete mixed-graph recovery across fields: source queries and interpolation
weights stay in K; target products and the final answer lie in L. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.CrossFieldMixedRecovery
open Complexity Complexity.MixedCode ExponentProductSemantics SourceExponentRepresentatives
open CrossFieldInterpolationSemantics
variable {K L : Type} [Field K] [Field L] [DecidableEq K]
variable {q bt ut : ℕ}

omit [DecidableEq K] in
private theorem map_binaryRemainder (φ : K →+* L) (g : MixedCode) (selected : ℕ)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (σ : Fin g.vertices → Fin q) :
    φ (binaryRemainder g selected M U w σ) =
      binaryRemainder g selected (fun l i j => φ (M l i j))
        (fun l i => φ (U l i)) (fun i => φ (w i)) σ := by
  simp [binaryRemainder, map_mul, map_prod, map_list_prod, List.map_map, Function.comp_def]

/-- This is exactly the semantic interface needed by the variable-field caller.
Only current-length collisions matter; original unaries/backgrounds and every
unselected matrix are retained through the given field inclusion. -/
theorem binary_recovery (φ : K →+* L) (g : MixedCode) (hg : g.Valid bt ut)
    (selected : Fin bt) (M : Fin bt → Matrix (Fin q) (Fin q) K)
    (M' : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (hunchanged : ∀ l, l.val ≠ selected.val → M' l = fun i j => φ (M l i j))
    (hsource : ∀ i j, M selected i j ≠ 0)
    (hcompat : CrossCompatibleAt (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
      (g.markedCount selected.val)) :
    aggregate φ (binaryAlphabet (M' selected))
      (representatives (binaryAlphabet (M selected)) (g.markedCount selected.val))
      (List.ofFn (fun h : Fin (representatives (binaryAlphabet (M selected))
        (g.markedCount selected.val)).length =>
        (g.parallelLabel selected.val (h.val+1)).evaluate
          (parallelLabel_valid selected.val (h.val+1) bt ut g hg) M U w)) =
      g.evaluate hg M' (fun l i => φ (U l i)) (fun i => φ (w i)) := by
  let A := binaryAlphabet (M selected)
  let B := binaryAlphabet (M' selected)
  let m := g.markedCount selected.val
  have hex (σ : Fin g.vertices → Fin q) :
      ∃ i : Fin (representatives A m).length,
        sourceNode A m i = selectedBinaryProduct g selected.val M σ ∧
        value B (exponents A m i) = selectedBinaryProduct g selected.val M' σ := by
    let xs := WordFrequencies.frequencies (selectedBinaryWord g hg selected σ)
    have hx := selectedBinaryWord_frequencies_mem g hg selected σ
    have hz : value A xs ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro e _
      exact pow_ne_zero _ (hsource _ _)
    obtain ⟨i, hi, ht⟩ := exists_node_for_weak A B hcompat xs hx hz
    exact ⟨i, hi.trans (selectedBinaryProduct_eq_exponent_value g hg selected M σ).symm,
      ht.trans (selectedBinaryProduct_eq_exponent_value g hg selected M' σ).symm⟩
  choose classOf hs ht using hex
  let rest := binaryRemainder g selected.val M U w
  have hy : (fun h : Fin (representatives A m).length =>
      (g.parallelLabel selected.val (h.val+1)).evaluate
        (parallelLabel_valid selected.val (h.val+1) bt ut g hg) M U w) =
      (fun h => ∑ σ, rest σ * sourceNode A m (classOf σ) ^ (h.val+1)) := by
    funext h
    rw [evaluate_parallelLabel_eq_power_sum g hg selected.val (h.val+1) M U w]
    exact Finset.sum_congr rfl fun σ _ => by rw [hs]
  rw [aggregate_computed_table φ A B m, hy]
  rw [crossField_grouped_queries φ classOf rest (sourceNode A m)
    (fun i => value B (exponents A m i)) (sourceNode_injective A m) (sourceNode_nonzero A m)]
  rw [evaluate_eq_binary_product_sum g hg selected.val M' (fun l i => φ (U l i)) (fun i => φ (w i))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ht]
  congr 1
  rw [map_binaryRemainder]
  exact (binaryRemainder_congr g selected.val (fun l i j => φ (M l i j)) M'
    (fun l i => φ (U l i)) (fun i => φ (w i)) hunchanged σ).symm

end PlanarHom.CrossFieldMixedRecovery
