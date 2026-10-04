import PlanarHom.TensorSumEigenvalues
import PlanarHom.FixedFieldArithmeticMachines
import Mathlib.RingTheory.Trace.Basic

/-! # Explicit coordinate annihilators for promised number-field power roots

A cyclic block lift of multiplication by `c^n*y`, followed by a fixed tensor
sum, yields a rational matrix whose characteristic polynomial annihilates
`trace(c*x)` whenever `x^n=y`. Trace-dual choices of `c` give every coordinate.
This is an algebraic construction, not a root-extraction complexity theorem.
-/

noncomputable section
namespace PlanarHom.PowerRootCoordinateAnnihilator
open scoped BigOperators
open Matrix IntegerCoordinateBounds PowerRootLiftMatrix

variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)

abbrev Closure := AlgebraicClosure ℚ

def dual (i : Fin d) : K :=
  (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) basis i

theorem trace_dual_coordinate (i : Fin d) (x : K) :
    Algebra.trace ℚ K (dual basis i * x) = basis.equivFun x i := by
  have hd (j : Fin d) : Algebra.trace ℚ K (dual basis i * basis j) =
      if j = i then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left (Algebra.traceForm ℚ K)
      (traceForm_nondegenerate ℚ K) basis i j
  conv_lhs => rw [← basis.sum_equivFun x]
  simp only [Finset.mul_sum, Algebra.mul_smul_comm, map_sum, map_smul, hd,
    smul_eq_mul]
  simp

theorem multiplication_embedding_eigen (a : K) (σ : K →ₐ[ℚ] Closure) :
    ((multiplicationMatrix basis a).transpose.map (algebraMap ℚ Closure)) *ᵥ
      (fun j => σ (basis j)) = σ a • (fun j => σ (basis j)) := by
  funext j
  have h := congrArg σ (basis.sum_repr (basis j * a))
  simpa [Matrix.mulVec, dotProduct, multiplicationMatrix,
    LinearMap.toMatrix_apply, map_sum, Algebra.smul_def, mul_comm] using h

theorem embedding_vector_ne_zero (σ : K →ₐ[ℚ] Closure) :
    (fun j => σ (basis j)) ≠ 0 := by
  letI : Nonempty (Fin d) := basis.index_nonempty
  obtain ⟨j⟩ := ‹Nonempty (Fin d)›
  intro h
  have hz := congrFun h j
  exact ((map_ne_zero σ).mpr (basis.ne_zero j)) hz

def rootMatrix (n : ℕ) (c y : K) :=
  lift n (multiplicationMatrix basis (c^n*y)).transpose

theorem rootMatrix_eigen (n : ℕ) (hn : 0 < n) (c x : K)
    (σ : K →ₐ[ℚ] Closure) :
    ∃ v : Fin n × Fin d → Closure, v ≠ 0 ∧
      (rootMatrix basis n c (x^n)).map (algebraMap ℚ Closure) *ᵥ v =
        σ (c*x) • v := by
  let v := fun j => σ (basis j)
  refine ⟨eigenvector n (σ (c*x)) v,
    eigenvector_ne_zero n hn _ v (embedding_vector_ne_zero basis σ), ?_⟩
  rw [rootMatrix, lift_map]
  apply lift_eigen
  have h := multiplication_embedding_eigen basis (c^n*x^n) σ
  simpa only [← mul_pow, map_pow] using h

local instance : Fintype (K →ₐ[ℚ] Closure) := Fintype.ofFinite _

def traceMatrix (n : ℕ) (c y : K) :=
  TensorSumEigenvalues.matrix (Fintype.card (K →ₐ[ℚ] Closure)) (rootMatrix basis n c y)

def tracePolynomial (n : ℕ) (c y : K) : Polynomial ℚ :=
  (traceMatrix basis n c y).charpoly

theorem tracePolynomial_monic (n : ℕ) (c y : K) :
    (tracePolynomial basis n c y).Monic := Matrix.charpoly_monic _

theorem tracePolynomial_root (n : ℕ) (hn : 0 < n) (c x : K) :
    (tracePolynomial basis n c (x^n)).eval (Algebra.trace ℚ K (c*x)) = 0 := by
  let σs := (Finset.univ : Finset (K →ₐ[ℚ] Closure)).toList
  let rs := σs.map (fun σ => σ (c*x))
  have hlen : rs.length = Fintype.card (K →ₐ[ℚ] Closure) := by
    simp [rs, σs]
  have hsum : rs.sum = algebraMap ℚ Closure (Algebra.trace ℚ K (c*x)) := by
    rw [trace_eq_sum_embeddings Closure]
    simp [rs, σs]
    congr 1
    ext σ
    simp
  have he : ∀ r ∈ rs, ∃ v : Fin n × Fin d → Closure, v ≠ 0 ∧
      (rootMatrix basis n c (x^n)).map (algebraMap ℚ Closure) *ᵥ v = r • v := by
    intro r hr
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hr
    exact rootMatrix_eigen basis n hn c x σ
  have h := TensorSumEigenvalues.charpoly_sum_roots _ rs he
  rw [hlen, hsum, ← TensorSumEigenvalues.matrix_map, Matrix.charpoly_map,
    Polynomial.eval_map] at h
  apply (algebraMap ℚ Closure).injective
  simpa only [tracePolynomial, traceMatrix, Polynomial.eval₂_at_apply, map_zero] using h

def coordinatePolynomial (n : ℕ) (i : Fin d) (y : K) : Polynomial ℚ :=
  tracePolynomial basis n (dual basis i) y

/-- The degree is fixed independently of the input field value. -/
def coordinateDegree (n : ℕ) : ℕ :=
  (n*d) ^ Fintype.card (K →ₐ[ℚ] Closure)

include basis in
theorem coordinateDegree_eq (n : ℕ) : coordinateDegree (K:=K) (d:=d) n = (n*d)^d := by
  have h : Fintype.card (K →ₐ[ℚ] Closure) = Module.finrank ℚ K := by
    simpa only [Fintype.card_eq_nat_card] using AlgHom.card ℚ K Closure
  rw [coordinateDegree, h, Module.finrank_eq_card_basis basis]
  simp

theorem coordinatePolynomial_natDegree (n : ℕ) (i : Fin d) (y : K) :
    (coordinatePolynomial basis n i y).natDegree = coordinateDegree (K:=K) (d:=d) n := by
  simp [coordinatePolynomial, tracePolynomial, traceMatrix, Matrix.charpoly_natDegree_eq_dim,
    TensorSumEigenvalues.card_index, coordinateDegree, Fintype.card_prod]

theorem coordinatePolynomial_natDegree_eq (n : ℕ) (i : Fin d) (y : K) :
    (coordinatePolynomial basis n i y).natDegree = (n*d)^d :=
  (coordinatePolynomial_natDegree basis n i y).trans (coordinateDegree_eq basis n)

theorem coordinatePolynomial_monic (n : ℕ) (i : Fin d) (y : K) :
    (coordinatePolynomial basis n i y).Monic := tracePolynomial_monic basis n _ y

theorem coordinatePolynomial_root (n : ℕ) (hn : 0 < n) (i : Fin d) (x : K) :
    (coordinatePolynomial basis n i (x^n)).eval (basis.equivFun x i) = 0 := by
  rw [← trace_dual_coordinate basis i x]
  exact tracePolynomial_root basis n hn _ x

end PlanarHom.PowerRootCoordinateAnnihilator
