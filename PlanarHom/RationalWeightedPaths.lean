import PlanarHom.WeightedPathComparison
import PlanarHom.RationalLeadingSamples

/-!
# Weighted shortest paths from positive rational logarithmic support preservation

The source maximality argument controls positive rational parameters. We prove
that this already suffices for equation (4.2) and the weighted-shortest-path
conclusion, without assuming real-parameter support or analytic continuation.
Positive rational samples with quadratic accuracy preserve the required even
leading coefficients.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A positive integer Schur power equals the identity at the zero parameter. -/
theorem schurExp_zero (L : Matrix V V ℝ) (s : ℕ) (hs : 0 < s) : schurExp L s 0 = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [schurExp]
  · simp [schurExp, hij, zero_pow (Nat.ne_of_gt hs)]

/-- The actual spectral log of the Schur curve is zero at zero. -/
theorem matrixLog_schurExp_zero (L : Matrix V V ℝ) (s : ℕ) (hs : 0 < s) :
    EntropyCompletion.matrixLog (schurExp L s 0) = 0 := by
  rw [schurExp_zero L s hs]
  exact CFC.log_one

/-- Support on all sufficiently small positive rational parameters transfers
to the rationally sampled curve, including its zero parameter. -/
theorem sampled_schurLog_supported (L : Matrix V V ℝ) (G : SimpleGraph V)
    (s : ℕ) (hs : 0 < s)
    (hrational : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      SupportedOn G (EntropyCompletion.matrixLog (schurExp L s (q : ℝ)))) :
    ∀ᶠ t in 𝓝 0, SupportedOn G
      (EntropyCompletion.matrixLog (schurExp L s (rationalSampleReal t))) := by
  obtain ⟨ε, hε, hrat⟩ := hrational
  have hsmall := rationalSampleReal_tendsto.eventually_lt_const hε
  filter_upwards [hsmall] with t ht
  by_cases htzero : t = 0
  · subst t
    rw [rationalSampleReal_zero, matrixLog_schurExp_zero L s hs]
    intro i j hij hn
    rfl
  · exact hrat (positiveRationalSample t) (rationalSampleReal_pos htzero) ht

/-- Equation (4.2) follows from positive rational support preservation alone.
No real-parameter sparsity, moment identity, or desired coefficient is assumed. -/
theorem rational_schur_log_support_power_identity (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (s : ℕ) (hs : 0 < s) (heven : Even s)
    (hrational : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      SupportedOn (LogarithmicSupport.offDiagonalSupport L hL)
        (EntropyCompletion.matrixLog (schurExp L s (q : ℝ)))) (i j : V) :
    let d := (LogarithmicSupport.offDiagonalSupport L hL).dist i j
    (((L ^ d) i j) / (d.factorial : ℝ)) ^ s =
      (ShortestPathWeights.entrywisePow L s ^ d) i j / (d.factorial : ℝ) := by
  let G := LogarithmicSupport.offDiagonalSupport L hL
  let d := G.dist i j
  let A : ℝ → Matrix V V ℝ := fun t =>
    EntropyCompletion.matrixLog (schurExp L s (rationalSampleReal t))
  let B := ShortestPathWeights.entrywisePow L s
  have hsupport : ∀ᶠ t in 𝓝 0, SupportedOn G (A t) :=
    sampled_schurLog_supported L G s hs hrational
  have hB : SupportedOn G B := by
    intro a b hab hn
    dsimp [B, ShortestPathWeights.entrywisePow]
    rw [supportedOn_offDiagonalSupport L hL a b hab hn, zero_pow (Nat.ne_of_gt hs)]
  have horder : A =O[𝓝 0] (fun t : ℝ => t) :=
    ((matrixLog_schurExp_isBigO L hL s hs).comp_tendsto rationalSampleReal_tendsto).trans
      rationalSampleReal_isBigO
  have hdiag : ∀ a, (fun t => A t a a) =O[𝓝 0] (fun t : ℝ => t) :=
    fun a => entry_isBigO horder a a
  have hlead : ∀ a b, G.Adj a b →
      (fun t => A t a b - B a b * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
    intro a b hab
    exact leading_isBigO_comp_rationalSample ((L a b) ^ s) s heven
      (matrixLog_schurExp_entry_sub_leading_isBigO L hL s hs a b hab.1)
  have hright := supported_exp_distance_leading_isBigO G hG A B s hs hsupport hB hdiag hlead i j
  have heq := rationalSampleReal_tendsto.eventually (eventually_exp_matrixLog_schurExp L hL s hs)
  have hright' : (fun t => schurExp L s (rationalSampleReal t) i j -
      ((B ^ d) i j / (d.factorial : ℝ)) * t ^ (s * d)) =O[𝓝 0]
      (fun t : ℝ => t ^ (s * d + 1)) := by
    apply hright.congr'
    · filter_upwards [heq] with t ht
      rw [show NormedSpace.exp ℝ (A t) = schurExp L s (rationalSampleReal t) from ht]
    · rfl
  have hleft := pow_leading_isBigO ((L ^ d) i j / (d.factorial : ℝ)) d s
    (exp_entry_distance_leading_isBigO L hL i j)
  have hleft' : (fun t => schurExp L s t i j -
      ((L ^ d) i j / (d.factorial : ℝ)) ^ s * t ^ (s * d)) =O[𝓝 0]
        (fun t : ℝ => t ^ (s * d + 1)) := by
    simpa only [Nat.mul_comm d s, schurExp] using hleft
  have hsampled := leading_isBigO_comp_rationalSample
    (((L ^ d) i j / (d.factorial : ℝ)) ^ s) (s * d) (heven.mul_right d) hleft'
  exact leading_coefficient_unique _ _ (s * d) hsampled hright'

/-- The actual shortest-path conclusion needs only the rational support
preservation furnished by the source maximal-edge argument. -/
theorem shortest_paths_rigid_of_rational_schur_log_support (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hrational : ∀ s : ℕ, 0 < s → Even s → ∃ ε : ℝ, 0 < ε ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
        SupportedOn (LogarithmicSupport.offDiagonalSupport L hL)
          (EntropyCompletion.matrixLog (schurExp L s (q : ℝ)))) (i j : V) :
    Fintype.card (ShortestPathWeights.ShortestPath
      (LogarithmicSupport.offDiagonalSupport L hL) i j) =
        ((LogarithmicSupport.offDiagonalSupport L hL).dist i j).factorial ∧
      ∀ p q : ShortestPathWeights.ShortestPath (LogarithmicSupport.offDiagonalSupport L hL) i j,
        ShortestPathWeights.walkWeight L p.val = ShortestPathWeights.walkWeight L q.val := by
  apply ShortestPathWeights.shortestPath_card_and_weights_of_even_power_identities L
    (LogarithmicSupport.offDiagonalSupport L hL) hG (supportedOn_offDiagonalSupport L hL)
    hpositive i j
  intro s hs heven
  exact rational_schur_log_support_power_identity L hL hG s hs heven
    (hrational s hs heven) i j

end PlanarHom.MatrixLogCoefficients
