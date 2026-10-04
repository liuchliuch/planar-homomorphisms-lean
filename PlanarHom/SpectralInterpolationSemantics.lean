import PlanarHom.SelectedOccurrenceWords
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite spectral expansion of the actual mixed partition function

Every selected occurrence has its own projector choice, including parallel edges
and input loops. Unselected matrices, unaries, and backgrounds remain in the
signed coefficient. The expansion is valid for an empty selected list and for
zero spectral coefficients; it assumes no positivity of the companions.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
variable {C K : Type} [Fintype C] [CommSemiring K] {binaryTypes unaryTypes t : ℕ}

/-- Replace exactly one binary label by a linear combination of fixed matrices. -/
def spectralLabels (M : Fin binaryTypes → Matrix C C K) (selected : Fin binaryTypes)
    (P : Fin t → Matrix C C K) (a : Fin t → K) : Fin binaryTypes → Matrix C C K :=
  fun l => if l = selected then ∑ j, a j • P j else M l

/-- The endpoint colors of a selected occurrence in its original list position. -/
def spectralColors (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (σ : Fin g.vertices → C)
    (e : Fin (g.markedCount selected.val)) : C × C :=
  (selectedBinaryColors g hg selected σ).get
    ⟨e.val, by simpa only [selectedBinaryColors_length] using e.isLt⟩

/-- A projector tuple contributes the product of its chosen scalar eigenvalues. -/
def spectralProduct {m : ℕ} (a : Fin t → K) (choice : Fin m → Fin t) : K :=
  ∏ e, a (choice e)

/-- All unchanged constraints and selected projectors occur in this signed coefficient. -/
def spectralRest (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) (P : Fin t → Matrix C C K)
    (a : (Fin g.vertices → C) × (Fin (g.markedCount selected.val) → Fin t)) : K :=
  binaryRemainder g selected.val M U w a.1 *
    ∏ e, P (a.2 e) (spectralColors g hg selected a.1 e).1
      (spectralColors g hg selected a.1 e).2

private theorem selectedColors_prod (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (σ : Fin g.vertices → C) (f : C × C → K) :
    ((selectedBinaryColors g hg selected σ).map f).prod =
      ∏ e : Fin (g.markedCount selected.val), f (spectralColors g hg selected σ e) := by
  let xs := selectedBinaryColors g hg selected σ
  have hx : xs.length = g.markedCount selected.val := selectedBinaryColors_length _ _ _ _
  have he : (List.ofFn (fun e : Fin (g.markedCount selected.val) =>
      spectralColors g hg selected σ e)) = xs := by
    apply List.ext_getElem
    · simp [hx]
    · intro n hn hm
      simp [spectralColors, List.get_eq_getElem, xs]
  change (xs.map f).prod = _
  rw [← he, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Distribute all selected matrix sums over the actual projector-choice tuples. -/
theorem selectedBinaryProduct_spectral (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (P : Fin t → Matrix C C K) (a : Fin t → K) (σ : Fin g.vertices → C) :
    selectedBinaryProduct g selected.val (spectralLabels M selected P a) σ =
      ∑ choice : Fin (g.markedCount selected.val) → Fin t,
        (∏ e, P (choice e) (spectralColors g hg selected σ e).1
          (spectralColors g hg selected σ e).2) * spectralProduct a choice := by
  classical
  rw [← selectedBinaryColors_product g hg selected, selectedColors_prod]
  simp only [spectralLabels, ↓reduceIte, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro choice _
  rw [spectralProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  exact mul_comm _ _

/-- Exact finite expansion underlying source Lemma 3.3, with all original signed
companion constraints included in the coefficients. -/
theorem evaluate_spectral_expansion (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K)
    (P : Fin t → Matrix C C K) (a : Fin t → K) :
    g.evaluate hg (spectralLabels M selected P a) U w =
      ∑ z : (Fin g.vertices → C) × (Fin (g.markedCount selected.val) → Fin t),
        spectralRest g hg selected M U w P z * spectralProduct a z.2 := by
  classical
  rw [evaluate_eq_binary_product_sum g hg selected.val]
  simp_rw [binaryRemainder_congr g selected.val M (spectralLabels M selected P a) U w
    (fun l hl => by simp [spectralLabels, show l ≠ selected from fun he => hl (congrArg Fin.val he)])]
  simp_rw [selectedBinaryProduct_spectral g hg selected M P a, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro choice _
  simp only [spectralRest, mul_assoc]

/-- Spectral powers become powers of the complete tuple product. -/
theorem spectralProduct_pow {m : ℕ} (a : Fin t → K) (choice : Fin m → Fin t) (h : ℕ) :
    spectralProduct (fun i => a i ^ h) choice = spectralProduct a choice ^ h := by
  simp only [spectralProduct, Finset.prod_pow]

/-- Positive matrix-power queries have the exact scalar-product moment expansion. -/
theorem evaluate_spectral_powers (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K)
    (P : Fin t → Matrix C C K) (a : Fin t → K) (h : ℕ) :
    g.evaluate hg (spectralLabels M selected P (fun i => a i ^ h)) U w =
      ∑ z : (Fin g.vertices → C) × (Fin (g.markedCount selected.val) → Fin t),
        spectralRest g hg selected M U w P z * spectralProduct a z.2 ^ h := by
  rw [evaluate_spectral_expansion]
  simp_rw [spectralProduct_pow]

end PlanarHom.Complexity.MixedCode
