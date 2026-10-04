import PlanarHom.PositiveUnaryRationalPowers
import PlanarHom.FixedAlgebraicField
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Fixed algebraic spectral data

Algebraic entries give algebraic eigenvalues by the characteristic polynomial over
the field of real algebraic numbers. Finite Lagrange interpolation then proves
algebraicity of the actual continuous functional calculus whenever its values on
the spectrum are algebraic. No algebraicity of a chosen eigenbasis is asserted.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace PlanarHom.AlgebraicSpectralData
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every spectral value of a matrix with algebraic real entries is algebraic. -/
theorem isAlgebraic_of_mem_spectrum (A : Matrix V V ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) {x : ℝ} (hx : x ∈ spectrum ℝ A) :
    IsAlgebraic ℚ x := by
  let K := algebraicClosure ℚ ℝ
  let B : Matrix V V K := fun i j => ⟨A i j, mem_algebraicClosure_iff.mpr (hAlg i j)⟩
  have hmap : B.map (algebraMap K ℝ) = A := rfl
  have hroot : aeval x B.charpoly = 0 := by
    rw [← eval_map_algebraMap, ← Matrix.charpoly_map, hmap]
    exact (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hx)
  exact (show IsIntegral K x from ⟨B.charpoly, B.charpoly_monic, hroot⟩).trans_isAlgebraic ℚ

/-- The actual Hermitian spectral theorem's eigenvalues are algebraic. -/
theorem isAlgebraic_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (k : V) :
    IsAlgebraic ℚ (hA.eigenvalues k) :=
  isAlgebraic_of_mem_spectrum A hAlg (hA.eigenvalues_mem_spectrum_real k)

omit [DecidableEq V] in
/-- Products of matrices with algebraic entries have algebraic entries. -/
theorem isAlgebraic_mul_entry (A B : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic ℚ (A i j)) (hB : ∀ i j, IsAlgebraic ℚ (B i j))
    (i j : V) : IsAlgebraic ℚ ((A * B) i j) := by
  rw [Matrix.mul_apply]
  apply mem_algebraicClosure_iff.mp
  exact (algebraicClosure ℚ ℝ).sum_mem (fun k _ =>
    mem_algebraicClosure_iff.mpr ((hA i k).mul (hB k j)))

/-- Every natural power has algebraic entries. -/
theorem isAlgebraic_pow_entry (A : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic ℚ (A i j)) (n : ℕ) (i j : V) :
    IsAlgebraic ℚ ((A ^ n) i j) := by
  induction n generalizing i j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
  | succ n ih =>
      rw [pow_succ]
      exact isAlgebraic_mul_entry _ _ (fun i j => ih i j) hA i j

/-- Evaluating an algebraic-coefficient polynomial preserves entry algebraicity. -/
theorem isAlgebraic_aeval_entry (A : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic ℚ (A i j)) (p : ℝ[X])
    (hp : ∀ n, IsAlgebraic ℚ (p.coeff n)) (i j : V) :
    IsAlgebraic ℚ ((aeval A p) i j) := by
  rw [aeval_eq_sum_range]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply mem_algebraicClosure_iff.mp
  exact (algebraicClosure ℚ ℝ).sum_mem (fun n _ =>
    mem_algebraicClosure_iff.mpr ((hp n).mul (isAlgebraic_pow_entry A hA n i j)))

/-- On the finite spectrum, algebraic data admit a polynomial with algebraic
coefficients. The polynomial is constructed over the real algebraic-number field. -/
theorem exists_algebraic_interpolating_polynomial (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (hAlg : ∀ i j, IsAlgebraic ℚ (A i j))
    (f : ℝ → ℝ) (hf : ∀ x ∈ spectrum ℝ A, IsAlgebraic ℚ (f x)) :
    ∃ p : ℝ[X], (∀ n, IsAlgebraic ℚ (p.coeff n)) ∧
      ∀ x ∈ spectrum ℝ A, p.eval x = f x := by
  classical
  let K := algebraicClosure ℚ ℝ
  let nodes : V → K := fun i =>
    ⟨hA.eigenvalues i, mem_algebraicClosure_iff.mpr (isAlgebraic_eigenvalues A hA hAlg i)⟩
  let s : Finset K := Finset.univ.image nodes
  let values : K → K := fun x => if hx : (x : ℝ) ∈ spectrum ℝ A then
    ⟨f x, mem_algebraicClosure_iff.mpr (hf x hx)⟩ else 0
  let q : K[X] := Lagrange.interpolate s id values
  refine ⟨q.map (algebraMap K ℝ), ?_, ?_⟩
  · intro n
    rw [coeff_map]
    exact mem_algebraicClosure_iff.mp (q.coeff n).property
  · intro x hx
    obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
    have hnode : nodes i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have heval : q.eval (nodes i) = values (nodes i) :=
      Lagrange.eval_interpolate_at_node values (fun _ _ _ _ h => h) hnode
    have hvalues : ((values (nodes i) : K) : ℝ) = f (hA.eigenvalues i) := by
      simp only [values, nodes, dif_pos (hA.eigenvalues_mem_spectrum_real i)]
    calc
      (q.map (algebraMap K ℝ)).eval (hA.eigenvalues i) =
          (algebraMap K ℝ) (q.eval (nodes i)) := by
            rw [eval_map]
            exact eval₂_at_apply (algebraMap K ℝ) (nodes i)
      _ = f (hA.eigenvalues i) := by rw [heval]; exact hvalues

/-- The genuine finite-dimensional functional calculus preserves entry
algebraicity when its values on the spectrum are algebraic. -/
theorem isAlgebraic_cfc_entry (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ A, IsAlgebraic ℚ (f x)) (i j : V) :
    IsAlgebraic ℚ ((cfc f A) i j) := by
  obtain ⟨p, hp, heval⟩ := exists_algebraic_interpolating_polynomial A hA hAlg f hf
  have heq : cfc f A = aeval A p := by
    rw [← cfc_polynomial p A (show IsSelfAdjoint A from hA)]
    exact cfc_congr (fun x hx => (heval x hx).symm)
  rw [heq]
  exact isAlgebraic_aeval_entry A hAlg p hp i j

/-- The canonical projector for one distinct eigenvalue. Repeated eigenvalues
are handled together; no chosen rank-one eigenspace splitting is involved. -/
def spectralProjector (A : Matrix V V ℝ) (a : ℝ) : Matrix V V ℝ :=
  cfc (fun x : ℝ => if x = a then 1 else 0) A

/-- All entries of every canonical distinct-eigenvalue projector are algebraic. -/
theorem isAlgebraic_spectralProjector_entry (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (a : ℝ) (i j : V) :
    IsAlgebraic ℚ (spectralProjector A a i j) := by
  apply isAlgebraic_cfc_entry A hA hAlg
  intro x hx
  split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero

/-- The paper's orthogonal range projector for a PSD matrix. -/
def rangeProjector (A : Matrix V V ℝ) : Matrix V V ℝ :=
  cfc (fun x : ℝ => if 0 < x then 1 else 0) A

/-- Algebraicity of the exact range-projector entries. -/
theorem isAlgebraic_rangeProjector_entry (A : Matrix V V ℝ) (hA : A.PosSemidef)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (i j : V) :
    IsAlgebraic ℚ (rangeProjector A i j) := by
  apply isAlgebraic_cfc_entry A hA.1 hAlg
  intro x hx
  split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero

/-- A fixed rational power using the genuine real power functional calculus. -/
def rationalPower (A : Matrix V V ℝ) (r : ℚ) : Matrix V V ℝ :=
  cfc (fun x : ℝ => x ^ (r : ℝ)) A

/-- Fixed rational powers of a positive-definite algebraic matrix have
algebraic entries, including negative and zero exponents. -/
theorem isAlgebraic_rationalPower_entry (A : Matrix V V ℝ) (hA : A.PosDef)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (r : ℚ) (i j : V) :
    IsAlgebraic ℚ (rationalPower A r i j) := by
  apply isAlgebraic_cfc_entry A hA.1 hAlg
  intro x hx
  obtain ⟨k, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
  exact PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat (hA.eigenvalues_pos k)
    (isAlgebraic_eigenvalues A hA.1 hAlg k) r

/-- One actual finite rational extension contains every fixed original
constant, matrix entry, eigenvalue, canonical spectral-projector entry, and any
fixed finite family of algebraic functional-calculus entries. This is an
existence theorem for fixed data, not an eigenvalue algorithm for variable input. -/
theorem exists_fixed_finite_extension {D : Type*} [Finite D]
    (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (f : D → ℝ → ℝ)
    (hf : ∀ d x, x ∈ spectrum ℝ A → IsAlgebraic ℚ (f d x))
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ k, hA.eigenvalues k ∈ K) ∧
      (∀ k i j, spectralProjector A (hA.eigenvalues k) i j ∈ K) ∧
      (∀ d i j, (cfc (f d) A) i j ∈ K) := by
  let entries : V × V → ℝ := fun ij => A ij.1 ij.2
  let projectors : V × V × V → ℝ := fun kij =>
    spectralProjector A (hA.eigenvalues kij.1) kij.2.1 kij.2.2
  let functions : D × V × V → ℝ := fun dij => (cfc (f dij.1) A) dij.2.1 dij.2.2
  let T : Set ℝ := S ∪ Set.range entries ∪ Set.range hA.eigenvalues ∪
    Set.range projectors ∪ Set.range functions
  have hT : T.Finite := (((hS.union (Set.finite_range entries)).union
    (Set.finite_range hA.eigenvalues)).union (Set.finite_range projectors)).union
    (Set.finite_range functions)
  have hTAlg : ∀ x ∈ T, IsAlgebraic ℚ x := by
    intro x hx
    rcases hx with (((hx | ⟨⟨i, j⟩, rfl⟩) | ⟨k, rfl⟩) |
      ⟨⟨k, i, j⟩, rfl⟩) | ⟨⟨d, i, j⟩, rfl⟩
    · exact hSAlg x hx
    · exact hAlg i j
    · exact isAlgebraic_eigenvalues A hA hAlg k
    · exact isAlgebraic_spectralProjector_entry A hA hAlg _ i j
    · exact isAlgebraic_cfc_entry A hA hAlg (f d) (hf d) i j
  letI := hT.fintype
  let K := IntermediateField.adjoin ℚ T
  have hdim : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => (hTAlg x hx).isIntegral)
  have hmem : ∀ x ∈ T, x ∈ K := fun x hx => IntermediateField.subset_adjoin ℚ T hx
  refine ⟨K, hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hmem x (Or.inl (Or.inl (Or.inl (Or.inl hx))))
  · intro i j
    exact hmem _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
  · intro k
    exact hmem _ (Or.inl (Or.inl (Or.inr ⟨k, rfl⟩)))
  · intro k i j
    exact hmem _ (Or.inl (Or.inr ⟨(k, i, j), rfl⟩))
  · intro d i j
    exact hmem _ (Or.inr ⟨(d, i, j), rfl⟩)

/-- The fixed-field conclusion quantified directly over the distinct spectrum,
so it is independent of the chosen finite enumeration of spectral values. -/
theorem exists_fixed_finite_extension_spectrum {D : Type*} [Finite D]
    (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (f : D → ℝ → ℝ)
    (hf : ∀ d x, x ∈ spectrum ℝ A → IsAlgebraic ℚ (f d x))
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ x ∈ spectrum ℝ A, x ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, ∀ i j, spectralProjector A x i j ∈ K) ∧
      (∀ d i j, (cfc (f d) A) i j ∈ K) := by
  obtain ⟨K, hdim, hS', hA', heigen, hproj, hfun⟩ :=
    exists_fixed_finite_extension A hA hAlg f hf S hS hSAlg
  refine ⟨K, hdim, hS', hA', ?_, ?_, hfun⟩
  · intro x hx
    obtain ⟨k, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
    exact heigen k
  · intro x hx
    obtain ⟨k, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
    exact hproj k

/-- The fixed PSD matrix and its exact range projector share a finite field
with its spectral data and all original fixed algebraic constants. -/
theorem exists_fixed_finite_extension_rangeProjector (A : Matrix V V ℝ)
    (hA : A.PosSemidef) (hAlg : ∀ i j, IsAlgebraic ℚ (A i j))
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ x ∈ spectrum ℝ A, x ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, ∀ i j, spectralProjector A x i j ∈ K) ∧
      (∀ i j, rangeProjector A i j ∈ K) := by
  let f : Unit → ℝ → ℝ := fun _ x => if 0 < x then 1 else 0
  have hf : ∀ d x, x ∈ spectrum ℝ A → IsAlgebraic ℚ (f d x) := by
    intro d x hx
    dsimp [f]
    split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
  obtain ⟨K, hdim, hS', hA', heigen, hproj, hfun⟩ :=
    exists_fixed_finite_extension_spectrum A hA.1 hAlg f hf S hS hSAlg
  exact ⟨K, hdim, hS', hA', heigen, hproj, hfun ()⟩

/-- The exact constants required by both spectral-interpolation consequences
for a fixed positive-definite matrix and fixed rational exponent fit in one
finite field, together with every original fixed algebraic language constant. -/
theorem exists_fixed_finite_extension_rationalPower (A : Matrix V V ℝ)
    (hA : A.PosDef) (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (r : ℚ)
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ x ∈ spectrum ℝ A, x ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, ∀ i j, spectralProjector A x i j ∈ K) ∧
      (∀ i j, rangeProjector A i j ∈ K) ∧
      (∀ i j, rationalPower A r i j ∈ K) := by
  let f : Bool → ℝ → ℝ := fun b x =>
    if b then x ^ (r : ℝ) else if 0 < x then 1 else 0
  have hf : ∀ b x, x ∈ spectrum ℝ A → IsAlgebraic ℚ (f b x) := by
    intro b x hx
    cases b with
    | false =>
        simp only [f, Bool.false_eq_true, ↓reduceIte]
        split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
    | true =>
        simp only [f, ↓reduceIte]
        obtain ⟨k, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
        exact PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat (hA.eigenvalues_pos k)
          (isAlgebraic_eigenvalues A hA.1 hAlg k) r
  obtain ⟨K, hdim, hS', hA', heigen, hproj, hfun⟩ :=
    exists_fixed_finite_extension_spectrum A hA.1 hAlg f hf S hS hSAlg
  refine ⟨K, hdim, hS', hA', heigen, hproj, ?_, ?_⟩
  · simpa only [f, Bool.false_eq_true, ↓reduceIte] using hfun false
  · simpa only [f, ↓reduceIte] using hfun true

/-- The common field also contains the scalar target values themselves, as
needed for exact spectral-product recovery, in addition to the CFC entries. -/
theorem exists_fixed_finite_extension_spectralValues {D : Type*} [Finite D]
    (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (f : D → ℝ → ℝ)
    (hf : ∀ d x, x ∈ spectrum ℝ A → IsAlgebraic ℚ (f d x))
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ x ∈ spectrum ℝ A, x ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, ∀ i j, spectralProjector A x i j ∈ K) ∧
      (∀ d i j, (cfc (f d) A) i j ∈ K) ∧
      (∀ d x, x ∈ spectrum ℝ A → f d x ∈ K) := by
  let values : D × V → ℝ := fun dk => f dk.1 (hA.eigenvalues dk.2)
  let T : Set ℝ := S ∪ Set.range values
  have hT : T.Finite := hS.union (Set.finite_range values)
  have hTAlg : ∀ x ∈ T, IsAlgebraic ℚ x := by
    intro x hx
    rcases hx with hx | ⟨⟨d, k⟩, rfl⟩
    · exact hSAlg x hx
    · exact hf d _ (hA.eigenvalues_mem_spectrum_real k)
  obtain ⟨K, hdim, hT', hA', heigen, hproj, hfun⟩ :=
    exists_fixed_finite_extension_spectrum A hA hAlg f hf T hT hTAlg
  refine ⟨K, hdim, (fun x hx => hT' (Or.inl hx)), hA', heigen, hproj, hfun, ?_⟩
  intro d x hx
  obtain ⟨k, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  exact hT' (Or.inr ⟨(d, k), rfl⟩)

/-- All constants required for rational-power spectral recovery, including
the scalar eigenvalue powers, lie in one actual fixed finite rational field. -/
theorem exists_fixed_finite_extension_rationalPower_values (A : Matrix V V ℝ)
    (hA : A.PosDef) (hAlg : ∀ i j, IsAlgebraic ℚ (A i j)) (r : ℚ)
    (S : Set ℝ) (hS : S.Finite) (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      (∀ i j, A i j ∈ K) ∧ (∀ x ∈ spectrum ℝ A, x ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, ∀ i j, spectralProjector A x i j ∈ K) ∧
      (∀ i j, rangeProjector A i j ∈ K) ∧
      (∀ i j, rationalPower A r i j ∈ K) ∧
      (∀ x ∈ spectrum ℝ A, x ^ (r : ℝ) ∈ K) := by
  let values : V → ℝ := fun k => hA.1.eigenvalues k ^ (r : ℝ)
  let T : Set ℝ := S ∪ Set.range values
  have hT : T.Finite := hS.union (Set.finite_range values)
  have hTAlg : ∀ x ∈ T, IsAlgebraic ℚ x := by
    intro x hx
    rcases hx with hx | ⟨k, rfl⟩
    · exact hSAlg x hx
    · exact PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat (hA.eigenvalues_pos k)
        (isAlgebraic_eigenvalues A hA.1 hAlg k) r
  obtain ⟨K, hdim, hT', hA', heigen, hproj, hrange, hpow⟩ :=
    exists_fixed_finite_extension_rationalPower A hA hAlg r T hT hTAlg
  refine ⟨K, hdim, (fun x hx => hT' (Or.inl hx)), hA', heigen, hproj, hrange, hpow, ?_⟩
  intro x hx
  obtain ⟨k, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
  exact hT' (Or.inr ⟨k, rfl⟩)

end PlanarHom.AlgebraicSpectralData
