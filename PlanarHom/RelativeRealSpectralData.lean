import PlanarHom.AlgebraicSpectralData

/-! NEW relative spectral algebraicity. The base field may contain arbitrary
transcendental real constants. Eigenvalues follow from the actual characteristic
polynomial, and projector entries from finite polynomial interpolation. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace PlanarHom.RelativeRealSpectralData
open AlgebraicSpectralData (spectralProjector)
variable {F : Type} [Field F] [Algebra F ℝ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every spectral value of a matrix with algebraic real entries is algebraic. -/
theorem isAlgebraic_of_mem_spectrum (A : Matrix V V ℝ)
    (hAlg : ∀ i j, IsAlgebraic F (A i j)) {x : ℝ} (hx : x ∈ spectrum ℝ A) :
    IsAlgebraic F x := by
  let K := algebraicClosure F ℝ
  let B : Matrix V V K := fun i j => ⟨A i j, mem_algebraicClosure_iff.mpr (hAlg i j)⟩
  have hmap : B.map (algebraMap K ℝ) = A := rfl
  have hroot : aeval x B.charpoly = 0 := by
    rw [← eval_map_algebraMap, ← Matrix.charpoly_map, hmap]
    exact (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hx)
  exact (show IsIntegral K x from ⟨B.charpoly, B.charpoly_monic, hroot⟩).trans_isAlgebraic F

/-- The actual Hermitian spectral theorem's eigenvalues are algebraic. -/
theorem isAlgebraic_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic F (A i j)) (k : V) :
    IsAlgebraic F (hA.eigenvalues k) :=
  isAlgebraic_of_mem_spectrum A hAlg (hA.eigenvalues_mem_spectrum_real k)

omit [DecidableEq V] in
/-- Products of matrices with algebraic entries have algebraic entries. -/
theorem isAlgebraic_mul_entry (A B : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic F (A i j)) (hB : ∀ i j, IsAlgebraic F (B i j))
    (i j : V) : IsAlgebraic F ((A * B) i j) := by
  rw [Matrix.mul_apply]
  apply mem_algebraicClosure_iff.mp
  exact (algebraicClosure F ℝ).sum_mem (fun k _ =>
    mem_algebraicClosure_iff.mpr ((hA i k).mul (hB k j)))

/-- Every natural power has algebraic entries. -/
theorem isAlgebraic_pow_entry (A : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic F (A i j)) (n : ℕ) (i j : V) :
    IsAlgebraic F ((A ^ n) i j) := by
  induction n generalizing i j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
  | succ n ih =>
      rw [pow_succ]
      exact isAlgebraic_mul_entry _ _ (fun i j => ih i j) hA i j

/-- Evaluating an algebraic-coefficient polynomial preserves entry algebraicity. -/
theorem isAlgebraic_aeval_entry (A : Matrix V V ℝ)
    (hA : ∀ i j, IsAlgebraic F (A i j)) (p : ℝ[X])
    (hp : ∀ n, IsAlgebraic F (p.coeff n)) (i j : V) :
    IsAlgebraic F ((aeval A p) i j) := by
  rw [aeval_eq_sum_range]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply mem_algebraicClosure_iff.mp
  exact (algebraicClosure F ℝ).sum_mem (fun n _ =>
    mem_algebraicClosure_iff.mpr ((hp n).mul (isAlgebraic_pow_entry A hA n i j)))

/-- On the finite spectrum, algebraic data admit a polynomial with algebraic
coefficients. The polynomial is constructed over the real algebraic-number field. -/
theorem exists_algebraic_interpolating_polynomial (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (hAlg : ∀ i j, IsAlgebraic F (A i j))
    (f : ℝ → ℝ) (hf : ∀ x ∈ spectrum ℝ A, IsAlgebraic F (f x)) :
    ∃ p : ℝ[X], (∀ n, IsAlgebraic F (p.coeff n)) ∧
      ∀ x ∈ spectrum ℝ A, p.eval x = f x := by
  classical
  let K := algebraicClosure F ℝ
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
    (hAlg : ∀ i j, IsAlgebraic F (A i j)) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ A, IsAlgebraic F (f x)) (i j : V) :
    IsAlgebraic F ((cfc f A) i j) := by
  obtain ⟨p, hp, heval⟩ := exists_algebraic_interpolating_polynomial A hA hAlg f hf
  have heq : cfc f A = aeval A p := by
    rw [← cfc_polynomial p A (show IsSelfAdjoint A from hA)]
    exact cfc_congr (fun x hx => (heval x hx).symm)
  rw [heq]
  exact isAlgebraic_aeval_entry A hAlg p hp i j

/-- All entries of every canonical distinct-eigenvalue projector are algebraic. -/
theorem isAlgebraic_spectralProjector_entry (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hAlg : ∀ i j, IsAlgebraic F (A i j)) (a : ℝ) (i j : V) :
    IsAlgebraic F (spectralProjector A a i j) := by
  apply isAlgebraic_cfc_entry A hA hAlg
  intro x hx
  split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero


end PlanarHom.RelativeRealSpectralData
