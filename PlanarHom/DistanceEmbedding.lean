import PlanarHom.EntropyCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Matrix.Order

/-!
# Squared Euclidean realization of graph distance

The first step of Lemma 4.6: positivity of every graph-distance kernel on `(0,1)`
implies that graph distance is a squared Euclidean distance.
-/

open scoped BigOperators InnerProductSpace MatrixOrder
open Matrix

noncomputable section

namespace PlanarHom.EntropyCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The polynomial extension of `(1 - x^d)/(1 - x)` at `x = 1`. -/
def distanceGeomSum (G : SimpleGraph V) (x : ℝ) : Matrix V V ℝ :=
  fun i j => ∑ k ∈ Finset.range (G.dist i j), x ^ k

omit [Fintype V] [DecidableEq V] in
@[simp] theorem distanceGeomSum_one (G : SimpleGraph V) (i j : V) :
    distanceGeomSum G 1 i j = (G.dist i j : ℝ) := by
  simp [distanceGeomSum]

omit [Fintype V] [DecidableEq V] in
theorem continuous_distanceGeomSum (G : SimpleGraph V) :
    Continuous (distanceGeomSum G) := by
  apply continuous_matrix
  intro i j
  exact continuous_finset_sum _ fun k _ => continuous_id.pow k

omit [Fintype V] [DecidableEq V] in
theorem distanceKernel_geomSum (G : SimpleGraph V) (x : ℝ) :
    distanceKernel G x = Matrix.of (fun _ _ => (1 : ℝ)) -
      (1 - x) • distanceGeomSum G x := by
  ext i j
  have h := geom_sum_mul_neg x (G.dist i j)
  simp only [distanceKernel, distanceGeomSum, Matrix.of_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  nlinarith

omit [DecidableEq V] in
/-- Positivity near `1` forces the distance matrix to be conditionally negative. -/
theorem distance_conditionally_negative (G : SimpleGraph V)
    (hpsd : ∀ x : ℝ, 0 < x → x < 1 → (distanceKernel G x).PosSemidef)
    (z : V → ℝ) (hz : ∑ i, z i = 0) :
    z ⬝ᵥ ((fun i j => (G.dist i j : ℝ)) *ᵥ z) ≤ 0 := by
  let q : ℝ → ℝ := fun x => z ⬝ᵥ (distanceGeomSum G x *ᵥ z)
  have hq : Continuous q :=
    continuous_const.dotProduct ((continuous_distanceGeomSum G).matrix_mulVec continuous_const)
  have hclosed : IsClosed {x : ℝ | q x ≤ 0} := isClosed_le hq continuous_const
  have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ {x : ℝ | q x ≤ 0} := by
    intro x hx
    have h := (hpsd x hx.1 hx.2).2 z
    rw [distanceKernel_geomSum] at h
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    have hJ : z ⬝ᵥ (Matrix.of (fun _ _ => (1 : ℝ)) *ᵥ z) = 0 := by
      simp [Matrix.mulVec, dotProduct, hz]
    rw [hJ] at h
    have hpos : 0 < 1 - x := sub_pos.mpr hx.2
    change q x ≤ 0
    change 0 ≤ 0 - (1 - x) * q x at h
    nlinarith
  have hmem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  have h := closure_minimal hsubset hclosed hmem
  change q 1 ≤ 0 at h
  have hmat : distanceGeomSum G 1 = (fun i j => (G.dist i j : ℝ)) := by
    ext i j; exact distanceGeomSum_one G i j
  simpa only [q, hmat] using h

/-- The Gram matrix with the chosen vertex placed at the origin. -/
def distanceGram (G : SimpleGraph V) (o : V) : Matrix V V ℝ :=
  fun i j => ((G.dist i o : ℝ) + (G.dist j o : ℝ) - (G.dist i j : ℝ)) / 2

theorem distanceGram_posSemidef (G : SimpleGraph V) (o : V)
    (hpsd : ∀ x : ℝ, 0 < x → x < 1 → (distanceKernel G x).PosSemidef) :
    (distanceGram G o).PosSemidef := by
  constructor
  · ext i j
    simp [distanceGram, Matrix.conjTranspose_apply, G.dist_comm, add_comm]
  · intro z
    let D : Matrix V V ℝ := fun i j => (G.dist i j : ℝ)
    let s : ℝ := ∑ i, z i
    let d : V → ℝ := fun i => (G.dist i o : ℝ)
    let e : V → ℝ := Pi.single o 1
    have hw : ∑ i, (z - s • e) i = 0 := by
      simp [e, s, Pi.sub_apply, Pi.smul_apply, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have h := distance_conditionally_negative G hpsd (z - s • e) hw
    change (z - s • e) ⬝ᵥ (D *ᵥ (z - s • e)) ≤ 0 at h
    have hDe : D *ᵥ e = d := by
      rw [show e = Pi.single o 1 from rfl, Matrix.mulVec_single_one]
      rfl
    have heDz : e ⬝ᵥ (D *ᵥ z) = d ⬝ᵥ z := by
      simp only [e, single_dotProduct, one_mul, Matrix.mulVec, D, d]
      congr 1
      funext i
      rw [G.dist_comm]
    have hed : e ⬝ᵥ d = 0 := by simp [e, d]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hDe,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, heDz, hed, mul_zero, sub_zero] at h
    have hK : distanceGram G o = (1 / 2 : ℝ) •
        (Matrix.vecMulVec d (fun _ => 1) + Matrix.vecMulVec (fun _ => 1) d - D) := by
      ext i j
      simp [distanceGram, Matrix.vecMulVec, Matrix.smul_apply,
        Matrix.sub_apply, d, D]
      ring
    rw [hK]
    simp only [star_trivial, Matrix.smul_mulVec, Matrix.sub_mulVec,
      Matrix.add_mulVec, Matrix.vecMulVec_mulVec, dotProduct_smul,
      dotProduct_sub, dotProduct_add, smul_eq_mul]
    have hones : (fun (_ : V) => (1 : ℝ)) ⬝ᵥ z = s := by simp [dotProduct, s]
    have hzOnes : z ⬝ᵥ (fun (_ : V) => (1 : ℝ)) = s := by simp [dotProduct, s]
    rw [hones, hzOnes]
    rw [dotProduct_comm d z] at h ⊢
    simp only [op_smul_eq_smul, smul_eq_mul]
    nlinarith

/-- A genuine finite Euclidean Gram representation, constructed from the PSD square root. -/
theorem exists_euclidean_gram {K : Matrix V V ℝ} (hK : K.PosSemidef) :
    ∃ f : V → EuclideanSpace ℝ V, ∀ i j, ⟪f i, f j⟫_ℝ = K i j := by
  let B := CFC.sqrt K
  have hB : B.IsHermitian := (CFC.sqrt_nonneg K).posSemidef.1
  have hBB : B * Bᴴ = K := by
    rw [hB.eq]
    exact CFC.sqrt_mul_sqrt_self K hK.nonneg
  refine ⟨fun i => WithLp.toLp 2 (B i), ?_⟩
  intro i j
  have h := congrArg (fun A : Matrix V V ℝ => A i j) hBB
  simpa only [EuclideanSpace.inner_toLp_toLp, star_trivial, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, mul_comm] using h

/-- The squared-distance realization can put any specified base vertex at zero. -/
theorem exists_distance_embedding_at (G : SimpleGraph V) (hG : G.Connected) (o : V)
    (hpsd : ∀ x : ℝ, 0 < x → x < 1 → (distanceKernel G x).PosSemidef) :
    ∃ f : V → EuclideanSpace ℝ V, Function.Injective f ∧ f o = 0 ∧
      ∀ u v, ‖f u - f v‖ ^ 2 = (G.dist u v : ℝ) := by
  obtain ⟨f, hf⟩ := exists_euclidean_gram (distanceGram_posSemidef G o hpsd)
  have hd : ∀ u v, ‖f u - f v‖ ^ 2 = (G.dist u v : ℝ) := by
    intro u v
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hf, hf, hf]
    simp [distanceGram, G.dist_self]
    ring
  have ho : f o = 0 := by
    apply norm_eq_zero.mp
    apply (sq_eq_zero_iff).mp
    rw [← real_inner_self_eq_norm_sq, hf]
    simp [distanceGram, G.dist_self]
  refine ⟨f, ?_, ho, hd⟩
  intro u v huv
  have h := hd u v
  rw [huv, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  exact hG.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h.symm)

/-- If every graph-distance kernel on `(0,1)` is PSD, graph distance is squared
Euclidean distance. The realization is injective for a connected graph. -/
theorem exists_distance_embedding (G : SimpleGraph V) (hG : G.Connected)
    (hpsd : ∀ x : ℝ, 0 < x → x < 1 → (distanceKernel G x).PosSemidef) :
    ∃ f : V → EuclideanSpace ℝ V, Function.Injective f ∧
      ∀ u v, ‖f u - f v‖ ^ 2 = (G.dist u v : ℝ) := by
  obtain ⟨f, hi, _, hd⟩ :=
    exists_distance_embedding_at G hG (Classical.choice hG.nonempty) hpsd
  exact ⟨f, hi, hd⟩

end PlanarHom.EntropyCompletion
