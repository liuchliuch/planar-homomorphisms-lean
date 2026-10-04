import PlanarHom.ClosedFamilyCoordinateTransport

/-! All rational sandwich bounds from actual family membership and the one
global maximum. The series hypothesis is the literal symmetric three-edge
composition; its mixed planar gadget derivation is supplied separately. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixLogCoefficients SymmetricBCH SandwichMaximality
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def SymmetricSeriesClosed (A : Set (Matrix V V ℝ)) : Prop :=
  ∀ H ∈ A, H.IsHermitian → ∀ K ∈ A, K.IsHermitian → H * K * H ∈ A

theorem symmetricSeriesClosed_reindex (e : V ≃ W) (A : Set (Matrix V V ℝ))
    (hA : SymmetricSeriesClosed A) : SymmetricSeriesClosed (reindexedFamily e A) := by
  intro H hH hHerm K hK hKerm
  obtain ⟨H, hH, rfl⟩ := hH
  obtain ⟨K, hK, rfl⟩ := hK
  have hH' : H.IsHermitian := by
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using hHerm.submatrix e
  have hK' : K.IsHermitian := by
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using hKerm.submatrix e
  have hm := mem_reindexedFamily e A _ (hA H hH hH' K hK hK')
  change (Matrix.reindexAlgEquiv ℝ ℝ e) (H * K * H) ∈ reindexedFamily e A at hm
  rw [map_mul, map_mul] at hm
  exact hm

theorem exp_rat_log_mem (A : Set (Matrix V V ℝ)) (hA : SpectralParallelClosed A)
    (H : Matrix V V ℝ) (hH : H ∈ A) (hpd : H.PosDef) (r : ℚ) :
    NormedSpace.exp ℝ ((r : ℝ) • EntropyCompletion.matrixLog H) ∈ A := by
  rw [← SpectralProductZeros.realPower_eq_exp_smul_log H hpd]
  exact hA.rationalPower_mem H hH hpd r

/-- Every literal rational sandwich is supplied by rational powers and a
three-edge symmetric series composition. No positivity of its entries is used. -/
theorem rational_sandwich_mem (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M N : Matrix V V ℝ) (hM : M ∈ A) (hMpd : M.PosDef)
    (hN : N ∈ A) (hNpd : N.PosDef) (η q : ℚ) :
    sandwich (EntropyCompletion.matrixLog M) ((η : ℝ) • EntropyCompletion.matrixLog N) q ∈ A := by
  have hleft := exp_rat_log_mem A hA M hM hMpd (q / 2)
  have hmiddle := exp_rat_log_mem A hA N hN hNpd (q * η)
  have hleftHerm : (NormedSpace.exp ℝ (((q / 2 : ℚ) : ℝ) • EntropyCompletion.matrixLog M)).IsHermitian :=
    (ExponentialDual.exp_posDef (hermitian_smul (EntropyCompletion.matrixLog M) IsSelfAdjoint.log _)).1
  have hmiddleHerm : (NormedSpace.exp ℝ (((q * η : ℚ) : ℝ) • EntropyCompletion.matrixLog N)).IsHermitian :=
    (ExponentialDual.exp_posDef (hermitian_smul (EntropyCompletion.matrixLog N) IsSelfAdjoint.log _)).1
  have h := hseries _ hleft hleftHerm _ hmiddle hmiddleHerm
  simpa [sandwich, smul_smul, Rat.cast_div, Rat.cast_mul, div_eq_mul_inv] using h

theorem rational_squareSandwich_mem (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M N : Matrix V V ℝ) (hM : M ∈ A) (hMpd : M.PosDef)
    (hN : N ∈ A) (hNpd : N.PosDef) (η q : ℚ) :
    squareSandwich (EntropyCompletion.matrixLog M) (EntropyCompletion.matrixLog N) η q ∈ A := by
  have hm := rational_sandwich_mem A hA hseries M N hM hMpd hN hNpd η q
  convert hA.entrywiseProduct_mem _ hm _ hm using 1
  ext i j
  exact pow_two _

theorem rationalSquareSandwichEdgeBound (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hNpd : N.PosDef) :
    RationalSquareSandwichEdgeBound (EntropyCompletion.matrixLog M)
      (EntropyCompletion.matrixLog N) IsSelfAdjoint.log IsSelfAdjoint.log := by
  intro η _
  refine ⟨1, by norm_num, ?_⟩
  intro q _ _ hpd hc hn
  exact hmax _ ⟨rational_squareSandwich_mem A hA hseries M N hM.mem hM.posDef hN hNpd η q,
    hn, hpd, hc⟩

theorem support_connected_of_positive_entries (H : Matrix V V ℝ) (hH : H.IsHermitian)
    [Nonempty V] (hp : ∀ i j, 0 < H i j) : (offDiagonalSupport H hH).Connected := by
  constructor
  intro i j
  by_cases hij : i = j
  · subst j
    exact SimpleGraph.Reachable.refl _
  · exact (show (offDiagonalSupport H hH).Adj i j from ⟨hij, ne_of_gt (hp i j)⟩).reachable

/-- The outer PD member may differ from M, but its logarithmic edge count
must equal the same fixed maximum. This covers the actual uniform kernel. -/
theorem rationalSandwichEdgeBound_of_same_card (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M H N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hH : H ∈ A) (hHpd : H.PosDef) (hN : N ∈ A) (hNpd : N.PosDef)
    (hcard : (logSupport H).edgeFinset.card = (logSupport M).edgeFinset.card) :
    RationalSandwichEdgeBound (EntropyCompletion.matrixLog H)
      (EntropyCompletion.matrixLog N) IsSelfAdjoint.log := by
  letI : Nonempty V := hM.connected.nonempty
  intro η _
  refine ⟨1, by norm_num, ?_⟩
  intro q _ _ hpd hp
  have h := hmax _ ⟨rational_sandwich_mem A hA hseries H N hH hHpd hN hNpd η q,
    fun i j => (hp i j).le, hpd, support_connected_of_positive_entries _ hpd.1 hp⟩
  change _ ≤ (logSupport H).edgeFinset.card
  rw [hcard]
  exact h

theorem rationalSandwichEdgeBound (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hNpd : N.PosDef) :
    RationalSandwichEdgeBound (EntropyCompletion.matrixLog M)
      (EntropyCompletion.matrixLog N) IsSelfAdjoint.log :=
  rationalSandwichEdgeBound_of_same_card A hA hseries M M N hM hmax hM.mem hM.posDef hN hNpd rfl

theorem rationalSandwichSchurEdgeBound (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) (hseries : SymmetricSeriesClosed A)
    (M N : Matrix V V ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hN : N ∈ A) (hNpd : N.PosDef) :
    RationalSandwichSchurEdgeBound (EntropyCompletion.matrixLog M)
      (EntropyCompletion.matrixLog N) IsSelfAdjoint.log := by
  intro η q _ _ hpd _ s hs _
  refine ⟨1, by norm_num, ?_⟩
  intro u _ _ hupd hconn hnonneg
  exact hmax _ ⟨schurExp_log_mem_of_posDef A hA _
    (rational_sandwich_mem A hA hseries M N hM.mem hM.posDef hN hNpd η q) hpd s hs u,
    hnonneg, hupd, hconn⟩

end PlanarHom.ClosedMatrixFamily
