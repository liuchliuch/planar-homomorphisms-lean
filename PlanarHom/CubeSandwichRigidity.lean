import PlanarHom.CubeSandwichGeometry
import PlanarHom.SandwichSquareRigidity
import PlanarHom.CubeLocalBlocks
import PlanarHom.CubeTensorCanonical

/-!
# Cube tensor rigidity from explicit rational candidate bounds

All support, opposite-edge, affine-diagonal and tensor identities are derived
from actual matrix curves. The remaining premises are numerical edge-count
bounds for named rational candidates; their joint-availability justification
is not silently assumed or claimed as proved.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
namespace PlanarHom.CubeSandwichRigidity
open Boolean LogarithmicSupport MatrixLogCoefficients SandwichMaximality
open SymmetricBCH MaximumLogarithmicSupport CubeTensorExponential

variable {d : ℕ}

/-- The square-candidate bound forces support on genuine cube edges. -/
theorem cube_support_of_square_maximality
    (C B : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB) :
    ∀ z w, z ≠ w → (∀ r, w ≠ Boolean.flip z r) → B z w = 0 := by
  have hG : (offDiagonalSupport C hC).Connected := by rw [hCube]; exact cubeGraph_connected d
  have hs := supportedOn_of_rational_squareSandwich_maximality C B hC hB hG hedge hsquare
  intro z w hzw hn
  apply hs z w hzw
  rw [hCube]
  intro ha
  obtain ⟨r, hr⟩ := (hammingGraph_adj_iff_flip z w).mp ha
  exact hn r hr

/-- Concrete cube squares transfer actual rational candidate rigidity to all
opposite entries of B. -/
theorem cube_opposite_of_sandwich_maximality
    (C B : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC)
    (hschur : RationalSandwichSchurEdgeBound C B hC) :
    ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      B z (Boolean.flip z r) = B (Boolean.flip z s) (Boolean.flip (Boolean.flip z s) r) := by
  have hG : (offDiagonalSupport C hC).Connected := by rw [hCube]; exact cubeGraph_connected d
  intro z r s hrs
  have h₁₂ := cubeGraph_adj_flip z r
  have h₂₃ := cubeGraph_adj_flip (Boolean.flip z r) s
  have h₃₄ : (cubeGraph d).Adj (Boolean.flip (Boolean.flip z r) s) (Boolean.flip z s) := by
    rw [flips_commute z r s]
    exact (cubeGraph_adj_flip (Boolean.flip z s) r).symm
  have h₄₁ := (cubeGraph_adj_flip z s).symm
  have h := opposite_square_entries_of_sandwich_maximality C B hC hB hG hedge hsquare hraw hschur
    z (Boolean.flip z r) (Boolean.flip (Boolean.flip z r) s) (Boolean.flip z s)
    (by simpa only [hCube] using h₁₂) (by simpa only [hCube] using h₂₃)
    (by simpa only [hCube] using h₃₄) (by simpa only [hCube] using h₄₁)
    (by simpa only [hCube] using cubeGraph_dist_two_flips z r s hrs)
    (by simpa only [hCube] using cubeGraph_dist_distinct_flips z r s hrs)
  calc
    B z (Boolean.flip z r) = B (Boolean.flip (Boolean.flip z r) s) (Boolean.flip z s) := h.2.2.1
    _ = B (Boolean.flip z s) (Boolean.flip (Boolean.flip z r) s) := by
      simpa only [star_trivial] using hB.apply (Boolean.flip z s) (Boolean.flip (Boolean.flip z r) s)
    _ = _ := by rw [flips_commute z r s]

/-- Raw rational maximality for a positive uniform outer direction operator
supplies the actual nonedge-zero sector required by the BCH theorem. -/
theorem uniform_nonedge_log_sector_of_maximality
    (B : Matrix (Cube d) (Cube d) ℝ) (hB : B.IsHermitian)
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ Boolean.flip z r) → B z w = 0)
    (c b : ℝ) (hb : 0 < b)
    (hmax : RationalSandwichEdgeBound (uniformDirectionMatrix d c b) B
      (uniformDirectionMatrix_isHermitian d c b)) :
    ∀ z w, z ≠ w → (∀ r, w ≠ Boolean.flip z r) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℚ, 0 < (η : ℝ) → (η : ℝ) < δ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
          EntropyCompletion.matrixLog
            (sandwich (uniformDirectionMatrix d c b) ((η : ℝ) • B) (q : ℝ)) z w = 0 := by
  let U := uniformDirectionMatrix d c b
  have hU := uniformDirectionMatrix_isHermitian d c b
  have hUgraph : offDiagonalSupport U hU = cubeGraph d := uniformDirectionMatrix_support c b (ne_of_gt hb)
  have hUconn : (offDiagonalSupport U hU).Connected := by rw [hUgraph]; exact cubeGraph_connected d
  have hUpos : ∀ z w, (offDiagonalSupport U hU).Adj z w → 0 < U z w := by
    intro z w h
    exact uniformDirectionMatrix_edge_pos c b hb z w (hUgraph ▸ h)
  have hs : SupportedOn (offDiagonalSupport U hU) B := by
    intro z w hzw hn
    apply hsupport z w hzw
    intro r hr
    apply hn
    rw [hUgraph, hr]
    exact cubeGraph_adj_flip z r
  obtain ⟨δ, hδ, hr⟩ := rational_sandwich_logSupport_eq_of_maximal U B hU hB hUconn hUpos hs hmax
  intro z w hzw hn
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  obtain ⟨ε, hε, hq⟩ := hr η (by exact_mod_cast hη) hηδ
  refine ⟨ε, hε, ?_⟩
  intro q hqpos hqε
  obtain ⟨hpd, hentry, heq, hlog⟩ := hq q (by exact_mod_cast hqpos) hqε
  by_contra hne
  have ha : (logSupport (sandwich U ((η : ℝ) • B) q)).Adj z w := ⟨hzw, hne⟩
  have hacube : (cubeGraph d).Adj z w := hUgraph ▸ (heq ▸ ha)
  obtain ⟨r, hr⟩ := (hammingGraph_adj_iff_flip z w).mp hacube
  exact hn r hr

/-- Affineness of the actual diagonal follows from numerical rational bounds,
with no support, opposite-edge or BCH-sector conclusion assumed. -/
theorem diagonal_affine_of_sandwich_maximality
    (C B : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC)
    (hschur : RationalSandwichSchurEdgeBound C B hC)
    (c b : ℝ) (hb : 0 < b)
    (hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b) B
      (uniformDirectionMatrix_isHermitian d c b)) (z : Cube d) :
    B z z = B (fun _ => false) (fun _ => false) +
      ∑ r, (B (unitBit r) (unitBit r) - B (fun _ => false) (fun _ => false)) *
        (if z r then 1 else 0) := by
  have hs := cube_support_of_square_maximality C B hC hB hCube hedge hsquare
  have ho := cube_opposite_of_sandwich_maximality C B hC hB hCube hedge hsquare hraw hschur
  have hsym : ∀ z w, B z w = B w z := fun z w => by
    simpa only [star_trivial] using hB.apply w z
  exact diagonal_affine_of_rational_log_sector B hsym ho hs c (fun _ => b)
    (fun _ => ne_of_gt hb) (uniform_nonedge_log_sector_of_maximality B hB hs c b hb hUniform) z

/-- The actual matrix exponential is a tensor of explicit two-by-two block
exponentials under the numerical rational-candidate bounds. -/
theorem exp_eq_tensor_of_sandwich_maximality
    (C B : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC)
    (hschur : RationalSandwichSchurEdgeBound C B hC)
    (c b : ℝ) (hb : 0 < b)
    (hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b) B
      (uniformDirectionMatrix_isHermitian d c b)) :
    NormedSpace.exp ℝ B = Real.exp (B (fun _ => false) (fun _ => false)) •
      CubeTensorExponential.tensor (fun r : Fin d => NormedSpace.exp ℝ
        (localBlock (B (unitBit r) (unitBit r) - B (fun _ => false) (fun _ => false))
          (B (fun _ => false) (unitBit r)))) := by
  have hs := cube_support_of_square_maximality C B hC hB hCube hedge hsquare
  have ho := cube_opposite_of_sandwich_maximality C B hC hB hCube hedge hsquare hraw hschur
  have hsym : ∀ z w, B z w = B w z := fun z w => by
    simpa only [star_trivial] using hB.apply w z
  apply exp_eq_tensor_localBlocks B (B (fun _ => false) (fun _ => false))
    (fun r => B (unitBit r) (unitBit r) - B (fun _ => false) (fun _ => false))
    (fun r => B (fun _ => false) (unitBit r))
  · intro z
    simpa only [mul_ite, mul_one, mul_zero] using
      diagonal_affine_of_sandwich_maximality C B hC hB hCube hedge hsquare hraw hschur c b hb hUniform z
  · exact fun z r => direction_weight_constant B hsym ho z r
  · exact hs

/-- The single-coordinate true color is the source's standard unit bit. -/
theorem oneCoordinate_true_eq_unitBit (r : Fin d) : oneCoordinate r true = unitBit r := by
  funext k
  by_cases hk : k = r
  · subst k; simp [oneCoordinate, zeroColor, unitBit]
  · simp [oneCoordinate, zeroColor, unitBit, Function.update_of_ne hk, hk]

/-- Canonical positive algebraic two-by-two factors of the original matrix,
with support, square rigidity and affine potential all derived from explicit
numerical rational-candidate bounds. This does not claim those bounds' separate
joint-availability justification. -/
theorem canonical_tensor_of_sandwich_maximality
    (C N : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hN : N.PosDef)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC IsSelfAdjoint.log)
    (hraw : RationalSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hschur : RationalSandwichSchurEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (c b : ℝ) (hb : 0 < b)
    (hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b)
      (EntropyCompletion.matrixLog N) (uniformDirectionMatrix_isHermitian d c b))
    (hnonneg : ∀ z w, 0 ≤ N z w)
    (hconn : (offDiagonalSupport N hN.1).Connected)
    (hAlg : ∀ z w, IsAlgebraic ℚ (N z w)) :
    N = N zeroColor zeroColor • CubeTensorExponential.tensor (canonicalFactor N) ∧
      0 < N zeroColor zeroColor ∧
      ∀ r : Fin d, (canonicalFactor N r).PosDef ∧
        (∀ a b, 0 < canonicalFactor N r a b) ∧
        (∀ a b, IsAlgebraic ℚ (canonicalFactor N r a b)) ∧
        canonicalFactor N r false false = 1 := by
  let B := EntropyCompletion.matrixLog N
  let a := fun r : Fin d => B (unitBit r) (unitBit r) - B zeroColor zeroColor
  let w := fun r : Fin d => B zeroColor (unitBit r)
  let F := fun r : Fin d => NormedSpace.exp ℝ (localBlock (a r) (w r))
  let γ := Real.exp (B zeroColor zeroColor)
  have hfactor : N = γ • CubeTensorExponential.tensor F := by
    have h := exp_eq_tensor_of_sandwich_maximality C B hC IsSelfAdjoint.log
      hCube hedge hsquare hraw hschur c b hb hUniform
    rw [show NormedSpace.exp ℝ B = N from KernelContinuation.exp_matrixLog hN] at h
    exact h
  have hF : ∀ r, (F r).PosDef := fun r => exp_localBlock_posDef (a r) (w r)
  have hγ : 0 < γ := Real.exp_pos _
  have hdiag : ∀ r, F r false false ≠ 0 := fun r =>
    ne_of_gt (posDef_diagonal_pos _ (hF r) false)
  refine ⟨tensor_eq_canonical_factors N hN.1 γ F hfactor (ne_of_gt hγ) hdiag,
    posDef_diagonal_pos N hN zeroColor, ?_⟩
  intro r
  obtain ⟨hpd, hpos⟩ := canonicalFactor_posDef_and_pos N hN.1 γ F hfactor hγ hF hnonneg hconn r
  exact ⟨hpd, hpos, fun a b => canonicalFactor_isAlgebraic N hAlg r a b, rfl⟩

end PlanarHom.CubeSandwichRigidity
