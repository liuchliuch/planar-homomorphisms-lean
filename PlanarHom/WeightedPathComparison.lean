import PlanarHom.SparseExponentialLeading
import PlanarHom.ShortestPathWeights
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-!
# Weighted-shortest-path coefficient comparison

This proves the analytic equation (4.2) from local logarithmic support
preservation, using actual matrix exponentials, Schur powers, and spectral
logarithms. It then proves the factorial path count and equal path products.

Local support preservation remains an explicit structural hypothesis. Its
maximal-family derivation belongs to the separate simulation/maximality argument;
no matrix-family availability or maximality claim is asserted here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- In the unit norm ball, exponentiating the genuine spectral log recovers `I+Q`. -/
theorem exp_matrixLog_one_add_of_norm_lt (Q : Matrix V V ℝ) (hQ : Q.IsHermitian)
    (hnorm : ‖Q‖ < 1) :
    NormedSpace.exp ℝ (EntropyCompletion.matrixLog (1 + Q)) = 1 + Q := by
  have hpos : ∀ x ∈ spectrum ℝ Q, 0 < 1 + x := by
    intro x hx
    have hb : |x| ≤ ‖Q‖ := spectrum.norm_le_norm_of_mem hx
    have hl := (abs_le.mp hb).1
    linarith
  have hc : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (spectrum ℝ Q) :=
    ContinuousOn.log (by fun_prop) (fun x hx => ne_of_gt (hpos x hx))
  rw [matrixLog_one_add Q hQ hnorm]
  have hself : IsSelfAdjoint (cfc (fun x : ℝ => Real.log (1 + x)) Q) := cfc_predicate _ _
  rw [← CFC.real_exp_eq_normedSpace_exp hself,
    ← cfc_comp' Real.exp (fun x : ℝ => Real.log (1 + x)) Q (by fun_prop) hc
      (show IsSelfAdjoint Q from hQ)]
  calc
    _ = cfc (fun x : ℝ => 1 + x) Q := cfc_congr (fun x hx => Real.exp_log (hpos x hx))
    _ = 1 + Q := by
      rw [cfc_const_add 1 (fun x : ℝ => x) Q (by fun_prop)
        (show IsSelfAdjoint Q from hQ), cfc_id' ℝ Q (show IsSelfAdjoint Q from hQ), map_one]

/-- The actual log of a positive-integer Schur exponential is `O(t)` as a matrix. -/
theorem matrixLog_schurExp_isBigO (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (s : ℕ) (hs : 0 < s) :
    (fun t => EntropyCompletion.matrixLog (schurExp L s t)) =O[𝓝 0] (fun t : ℝ => t) := by
  let Q : ℝ → Matrix V V ℝ := fun t => schurExp L s t - 1
  have hQ : Q =O[𝓝 0] (fun t : ℝ => t) := schurExp_sub_one_isBigO L s hs
  have hz : Tendsto Q (𝓝 0) (𝓝 0) := hQ.trans_tendsto tendsto_id
  have hh : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian := Eventually.of_forall fun t =>
    (schurExp_isHermitian L hL s t).sub Matrix.isHermitian_one
  have hr := (matrixLog_sub_logTaylor_isBigO_pow Q hh hz 1 1 (by simpa using hQ)).trans
    (pow_isBigO_pow (show 1 ≤ 1 * (1 + 1) by omega))
  have hr' : (fun t => EntropyCompletion.matrixLog (1 + Q t) - Q t) =O[𝓝 0]
      (fun t : ℝ => t) := by simpa only [logTaylor_one, pow_one] using hr
  have heq : ∀ t, 1 + Q t = schurExp L s t := by intro t; dsimp [Q]; abel
  simpa only [sub_add_cancel, heq] using hr'.add hQ

/-- The true exponential/logarithm inverse identity holds along the Schur curve near zero. -/
theorem eventually_exp_matrixLog_schurExp (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (s : ℕ) (hs : 0 < s) :
    ∀ᶠ t in 𝓝 0, NormedSpace.exp ℝ (EntropyCompletion.matrixLog (schurExp L s t)) =
      schurExp L s t := by
  let Q : ℝ → Matrix V V ℝ := fun t => schurExp L s t - 1
  have hz : Tendsto Q (𝓝 0) (𝓝 0) :=
    (schurExp_sub_one_isBigO L s hs).trans_tendsto tendsto_id
  have hn : ∀ᶠ t in 𝓝 0, ‖Q t‖ < 1 := by
    apply Filter.Tendsto.eventually_lt_const zero_lt_one
    simpa using hz.norm
  filter_upwards [hn] with t ht
  have hh : (Q t).IsHermitian := (schurExp_isHermitian L hL s t).sub Matrix.isHermitian_one
  have heq : 1 + Q t = schurExp L s t := by dsimp [Q]; abel
  simpa only [heq] using exp_matrixLog_one_add_of_norm_lt (Q t) hh ht

/-- A matrix is supported on its genuine off-diagonal support graph. -/
theorem supportedOn_offDiagonalSupport (L : Matrix V V ℝ) (hL : L.IsHermitian) :
    SupportedOn (LogarithmicSupport.offDiagonalSupport L hL) L := by
  intro i j hij hnot
  by_contra hne
  exact hnot ⟨hij, hne⟩

/-- Equation (4.2) in matrix-power form, extracted from actual leading
coefficients once local logarithmic support preservation is known. -/
theorem schur_log_support_power_identity (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (s : ℕ) (hs : 0 < s)
    (hsupport : ∀ᶠ t in 𝓝 0,
      SupportedOn (LogarithmicSupport.offDiagonalSupport L hL)
        (EntropyCompletion.matrixLog (schurExp L s t))) (i j : V) :
    let d := (LogarithmicSupport.offDiagonalSupport L hL).dist i j
    (((L ^ d) i j) / (d.factorial : ℝ)) ^ s =
      (ShortestPathWeights.entrywisePow L s ^ d) i j / (d.factorial : ℝ) := by
  let G := LogarithmicSupport.offDiagonalSupport L hL
  let d := G.dist i j
  let A : ℝ → Matrix V V ℝ := fun t => EntropyCompletion.matrixLog (schurExp L s t)
  let B := ShortestPathWeights.entrywisePow L s
  have hB : SupportedOn G B := by
    intro a b hab hn
    dsimp [B, ShortestPathWeights.entrywisePow]
    rw [supportedOn_offDiagonalSupport L hL a b hab hn, zero_pow (Nat.ne_of_gt hs)]
  have hdiag : ∀ a, (fun t => A t a a) =O[𝓝 0] (fun t : ℝ => t) :=
    fun a => entry_isBigO (matrixLog_schurExp_isBigO L hL s hs) a a
  have hlead : ∀ a b, G.Adj a b →
      (fun t => A t a b - B a b * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
    intro a b hab
    exact matrixLog_schurExp_entry_sub_leading_isBigO L hL s hs a b hab.1
  have hright := supported_exp_distance_leading_isBigO G hG A B s hs hsupport hB hdiag hlead i j
  have heq := eventually_exp_matrixLog_schurExp L hL s hs
  have hright' : (fun t => schurExp L s t i j -
      ((B ^ d) i j / (d.factorial : ℝ)) * t ^ (s * d)) =O[𝓝 0]
      (fun t : ℝ => t ^ (s * d + 1)) := by
    apply hright.congr'
    · filter_upwards [heq] with t ht
      rw [show NormedSpace.exp ℝ (A t) = schurExp L s t from ht]
    · rfl
  have hleft := pow_leading_isBigO ((L ^ d) i j / (d.factorial : ℝ)) d s
    (exp_entry_distance_leading_isBigO L hL i j)
  have hleft' : (fun t => schurExp L s t i j -
      ((L ^ d) i j / (d.factorial : ℝ)) ^ s * t ^ (s * d)) =O[𝓝 0]
        (fun t : ℝ => t ^ (s * d + 1)) := by
    simpa only [Nat.mul_comm d s, schurExp] using hleft
  exact leading_coefficient_unique _ _ (s * d) hleft' hright'

/-- The weighted-shortest-path conclusion of Lemma 4.3 follows from actual
local support preservation for positive even Schur powers. The graph-family
maximality step supplying that preservation is kept separate and explicit. -/
theorem shortest_paths_rigid_of_schur_log_support (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hsupport : ∀ s : ℕ, 0 < s → Even s → ∀ᶠ t in 𝓝 0,
      SupportedOn (LogarithmicSupport.offDiagonalSupport L hL)
        (EntropyCompletion.matrixLog (schurExp L s t))) (i j : V) :
    Fintype.card (ShortestPathWeights.ShortestPath
      (LogarithmicSupport.offDiagonalSupport L hL) i j) =
        ((LogarithmicSupport.offDiagonalSupport L hL).dist i j).factorial ∧
      ∀ p q : ShortestPathWeights.ShortestPath (LogarithmicSupport.offDiagonalSupport L hL) i j,
        ShortestPathWeights.walkWeight L p.val = ShortestPathWeights.walkWeight L q.val := by
  apply ShortestPathWeights.shortestPath_card_and_weights_of_even_power_identities L
    (LogarithmicSupport.offDiagonalSupport L hL) hG (supportedOn_offDiagonalSupport L hL)
    hpositive i j
  intro s hs heven
  exact schur_log_support_power_identity L hL hG s hs (hsupport s hs heven) i j

end PlanarHom.MatrixLogCoefficients
