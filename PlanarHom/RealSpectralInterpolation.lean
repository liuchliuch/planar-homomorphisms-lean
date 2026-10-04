import PlanarHom.SpectralInterpolationRecovery
import PlanarHom.PositiveUnaryRationalPowers
import PlanarHom.AlgebraicSpectralData
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.EquivFin

/-!
# Genuine real spectral data and exact spectral interpolation

The scalar alphabet consists of the distinct elements of the actual real
spectrum, and the matrices are canonical CFC spectral projectors. Zero spectral
values are retained in this fixed alphabet and automatically excluded by the
computed nonzero-product table. Range projection and rational real powers are
then recovered from positive matrix powers with all mixed companions unchanged.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.RealSpectralInterpolation
open Complexity.MixedCode ProductCompatibility ExponentProductTables LagrangeRecovery
variable {C : Type} [Fintype C] [DecidableEq C]

/-- A fixed enumeration of the actual distinct real spectrum, including zero. -/
def spectrumEquiv (A : Matrix C C ℝ) : spectrum ℝ A ≃ Fin (Nat.card (spectrum ℝ A)) := by
  letI := Fintype.ofFinite (spectrum ℝ A)
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card).symm

/-- Actual distinct eigenvalues, with their membership proofs supplied by the spectrum. -/
def scalar (A : Matrix C C ℝ) (i : Fin (Nat.card (spectrum ℝ A))) : ℝ :=
  ((spectrumEquiv A).symm i).val

/-- Canonical projectors onto whole eigenspaces, independent of multiplicities. -/
def projector (A : Matrix C C ℝ) (i : Fin (Nat.card (spectrum ℝ A))) : Matrix C C ℝ :=
  AlgebraicSpectralData.spectralProjector A (scalar A i)

theorem scalar_mem (A : Matrix C C ℝ) (i : Fin (Nat.card (spectrum ℝ A))) :
    scalar A i ∈ spectrum ℝ A := ((spectrumEquiv A).symm i).property

theorem scalar_injective (A : Matrix C C ℝ) : Function.Injective (scalar A) := by
  intro i j hij
  exact (spectrumEquiv A).symm.injective (Subtype.ext hij)

theorem scalar_surjective (A : Matrix C C ℝ) (x : ℝ) (hx : x ∈ spectrum ℝ A) :
    ∃ i, scalar A i = x := by
  refine ⟨spectrumEquiv A ⟨x, hx⟩, ?_⟩
  simp [scalar]

/-- Finite spectral resolution for any bare scalar function, obtained from the
matrix CFC. No continuity assumption is necessary on a finite spectrum. -/
theorem cfc_eq_sum_projectors (A : Matrix C C ℝ) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (scalar A i) • projector A i := by
  classical
  calc
    cfc f A = cfc (∑ i : Fin (Nat.card (spectrum ℝ A)),
        fun x : ℝ => f (scalar A i) * (if x = scalar A i then 1 else 0)) A := by
      apply cfc_congr
      intro x hx
      obtain ⟨j, rfl⟩ := scalar_surjective A x hx
      simp only [Finset.sum_apply]
      have he (i) : scalar A j = scalar A i ↔ j = i := (scalar_injective A).eq_iff
      simp [he]
    _ = ∑ i, f (scalar A i) • projector A i := by
      rw [cfc_sum_univ _ _ (fun _ => A.finite_real_spectrum.continuousOn _)]
      apply Finset.sum_congr rfl
      intro i _
      exact cfc_const_mul _ _ _ (A.finite_real_spectrum.continuousOn _)

/-- Genuine matrix powers have the required finite spectral expansion. -/
theorem matrix_pow_eq (A : Matrix C C ℝ) (hA : A.IsHermitian) (h : ℕ) :
    A ^ h = ∑ i, scalar A i ^ h • projector A i := by
  rw [← cfc_pow_id (R := ℝ) A h hA]
  exact cfc_eq_sum_projectors A (fun x => x ^ h)

/-- The source range projector is the actual positive-spectrum functional calculus. -/
def rangeProjector (A : Matrix C C ℝ) : Matrix C C ℝ :=
  AlgebraicSpectralData.rangeProjector A

/-- The source rational power uses the genuine real power at each eigenvalue. -/
def rationalPower (A : Matrix C C ℝ) (r : ℚ) : Matrix C C ℝ :=
  AlgebraicSpectralData.rationalPower A r

theorem scalar_nonneg (A : Matrix C C ℝ) (hA : A.PosSemidef)
    (i : Fin (Nat.card (spectrum ℝ A))) : 0 ≤ scalar A i := by
  have hi := scalar_mem A i
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hi
  obtain ⟨j, hj⟩ := hi
  exact hj ▸ hA.eigenvalues_nonneg j

theorem scalar_pos (A : Matrix C C ℝ) (hA : A.PosDef)
    (i : Fin (Nat.card (spectrum ℝ A))) : 0 < scalar A i := by
  have hi := scalar_mem A i
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hi
  obtain ⟨j, hj⟩ := hi
  exact hj ▸ hA.eigenvalues_pos j

/-- The indicator of the nonzero part preserves every nonzero source-product
collision; positivity is not needed for this purely algebraic statement. -/
theorem compatible_nonzero_indicator {I : Type} (a : I → ℝ) :
    Compatible a (fun i => if a i = 0 then 0 else 1) := by
  intro xs ys _ hxs hys _
  have hp (zs : List I) (hzs : ∀ i ∈ zs, a i ≠ 0) :
      (zs.map (fun i => if a i = 0 then (0 : ℝ) else 1)).prod = 1 := by
    have he : zs.map (fun i => if a i = 0 then (0 : ℝ) else 1) = zs.map (fun _ => 1) := by
      apply List.map_congr_left
      intro i hi
      simp [hzs i hi]
    simp [he]
  rw [hp xs hxs, hp ys hys]

theorem range_coefficients (A : Matrix C C ℝ) (hA : A.PosSemidef)
    (i : Fin (Nat.card (spectrum ℝ A))) :
    (if 0 < scalar A i then (1 : ℝ) else 0) = if scalar A i = 0 then 0 else 1 := by
  by_cases hi : scalar A i = 0
  · simp [hi]
  · simp [hi, lt_of_le_of_ne (scalar_nonneg A hA i) (Ne.symm hi)]

/-- The exact range projector has a zero-preserving, product-compatible spectral alphabet. -/
theorem rangeProjector_eq (A : Matrix C C ℝ) (hA : A.PosSemidef) :
    rangeProjector A = ∑ i, (if scalar A i = 0 then (0 : ℝ) else 1) • projector A i := by
  rw [rangeProjector, AlgebraicSpectralData.rangeProjector, cfc_eq_sum_projectors]
  simp_rw [range_coefficients A hA]

theorem rationalPower_eq (A : Matrix C C ℝ) (r : ℚ) :
    rationalPower A r = ∑ i, scalar A i ^ (r : ℝ) • projector A i :=
  cfc_eq_sum_projectors A (fun x => x ^ (r : ℝ))

variable {binaryTypes unaryTypes : ℕ}

/-- A spectral function satisfying precisely the scalar product hypotheses is
recovered from genuine positive matrix powers. The matrix power decomposition,
finite partition expansion, frequency coverage and Lagrange identity are all
proved, rather than included as assumptions. -/
theorem cfc_recovery (A : Matrix C C ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hzero : ∀ i, scalar A i = 0 → f (scalar A i) = 0)
    (hcompat : Compatible (scalar A) (fun i => f (scalar A i)))
    (g : Complexity.MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C ℝ)
    (U : Fin unaryTypes → C → ℝ) (w : C → ℝ) :
    evaluateReplacement (sourceNode (scalar A) (fun i => f (scalar A i)) (g.markedCount selected.val))
      (targetNode (scalar A) (fun i => f (scalar A i)) (g.markedCount selected.val))
      (fun h => g.evaluate hg (fun l => if l = selected then A ^ (h.val + 1) else M l) U w) =
      g.evaluate hg (fun l => if l = selected then cfc f A else M l) U w := by
  classical
  have h := spectral_matrix_power_recovery g hg selected M U w (projector A) A
    (scalar A) (fun i => f (scalar A i)) (fun n _ => matrix_pow_eq A hA n) hzero hcompat
  have hlabels : spectralLabels M selected (projector A) (fun i => f (scalar A i)) =
      (fun l => if l = selected then cfc f A else M l) := by
    funext l
    change (if l = selected then ∑ i, f (scalar A i) • projector A i else M l) = _
    rw [← cfc_eq_sum_projectors A f]
  rw [hlabels] at h
  exact h

/-- PSD range projection is recovered exactly from positive matrix powers,
including the zero matrix and a mixed instance with no selected occurrences. -/
theorem rangeProjector_recovery (A : Matrix C C ℝ) (hA : A.PosSemidef)
    (g : Complexity.MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C ℝ)
    (U : Fin unaryTypes → C → ℝ) (w : C → ℝ) :
    evaluateReplacement
      (sourceNode (scalar A) (fun i => if 0 < scalar A i then 1 else 0) (g.markedCount selected.val))
      (targetNode (scalar A) (fun i => if 0 < scalar A i then 1 else 0) (g.markedCount selected.val))
      (fun h => g.evaluate hg (fun l => if l = selected then A ^ (h.val + 1) else M l) U w) =
      g.evaluate hg (fun l => if l = selected then rangeProjector A else M l) U w := by
  classical
  apply cfc_recovery A hA.1 (fun x => if 0 < x then 1 else 0)
  · intro i hi
    simp [hi]
  · simpa only [range_coefficients A hA] using compatible_nonzero_indicator (scalar A)

/-- Every fixed rational real matrix power of a PD matrix is recovered by the
same exact source-product table, with no added product-map assumption. -/
theorem rationalPower_recovery (A : Matrix C C ℝ) (hA : A.PosDef) (r : ℚ)
    (g : Complexity.MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (selected : Fin binaryTypes) (M : Fin binaryTypes → Matrix C C ℝ)
    (U : Fin unaryTypes → C → ℝ) (w : C → ℝ) :
    evaluateReplacement
      (sourceNode (scalar A) (fun i => scalar A i ^ (r : ℝ)) (g.markedCount selected.val))
      (targetNode (scalar A) (fun i => scalar A i ^ (r : ℝ)) (g.markedCount selected.val))
      (fun h => g.evaluate hg (fun l => if l = selected then A ^ (h.val + 1) else M l) U w) =
      g.evaluate hg (fun l => if l = selected then rationalPower A r else M l) U w := by
  classical
  apply cfc_recovery A hA.1 (fun x => x ^ (r : ℝ))
  · intro i hi
    exact ((ne_of_gt (scalar_pos A hA i)) hi).elim
  · exact PositiveUnaryRationalPowers.compatible_real_rpow (scalar A) (scalar_pos A hA) r

end PlanarHom.RealSpectralInterpolation
