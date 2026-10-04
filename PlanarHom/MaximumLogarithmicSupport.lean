import PlanarHom.WheatstoneSupport
import PlanarHom.SchurExponentialLog

/-!
# Rational maximum-support preservation under even Schur powers

This is the analytic and finite-maximality layer of Lemmas 4.1 and 4.3.
The hypothesis bounding rational candidate edge counts is explicit; its
computational joint-availability justification is not postulated as a theorem.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MaximumLogarithmicSupport
open LogarithmicSupport MatrixLogCoefficients WheatstoneCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Hermitian curve tending to the identity is eventually positive definite. -/
theorem eventually_posDef_of_tendsto_one {α : Type*} {l : Filter α}
    (H : α → Matrix V V ℝ) (hH : ∀ᶠ t in l, (H t).IsHermitian)
    (ht : Tendsto H l (𝓝 1)) : ∀ᶠ t in l, (H t).PosDef := by
  have he (i : V) : ∀ᶠ t in l,
      (∑ j ∈ Finset.univ.erase i, ‖H t i j‖) < H t i i := by
    let margin : Matrix V V ℝ → ℝ := fun M => M i i - ∑ j ∈ Finset.univ.erase i, ‖M i j‖
    have hm : Continuous margin :=
      (continuous_id.matrix_elem i i).sub (continuous_finset_sum _
        (fun j _ => (continuous_id.matrix_elem i j).norm))
    have hzero : (∑ j ∈ Finset.univ.erase i, ‖(1 : Matrix V V ℝ) i j‖) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [Ne.symm (Finset.mem_erase.mp hj).1]
    have hmone : margin 1 = 1 := by
      change (1 : Matrix V V ℝ) i i - ∑ j ∈ Finset.univ.erase i, ‖(1 : Matrix V V ℝ) i j‖ = 1
      rw [hzero]
      simp
    have hlim : Tendsto (fun t => margin (H t)) l (𝓝 1) := by
      simpa only [hmone] using (hm.tendsto 1).comp ht
    exact (hlim.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono (fun t h => by
      change 0 < H t i i - ∑ j ∈ Finset.univ.erase i, ‖H t i j‖ at h
      linarith)
  filter_upwards [hH, eventually_all.mpr he] with t hherm hdom
  exact posDef_of_rowSum_lt_diagonal hherm hdom

/-- Positive integer Schur powers of an exponential are PD near zero; this
local statement suffices without invoking a global Schur-product theorem. -/
theorem eventually_posDef_schurExp (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (s : ℕ) (hs : 0 < s) : ∀ᶠ t in 𝓝 (0 : ℝ), (schurExp L s t).PosDef := by
  have hz := (schurExp_sub_one_isBigO L s hs).trans_tendsto tendsto_id
  have ht : Tendsto (schurExp L s) (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hz.add_const (1 : Matrix V V ℝ)
  exact eventually_posDef_of_tendsto_one _
    (Eventually.of_forall (fun t => schurExp_isHermitian L hL s t)) ht

/-- A nonzero entry of L persists positively in every positive even Schur power. -/
theorem eventually_schurExp_entry_pos (L : Matrix V V ℝ) (s : ℕ) (heven : Even s)
    (i j : V) (hij : i ≠ j) (hne : L i j ≠ 0) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, 0 < schurExp L s t i j :=
  eventually_pos_of_positive_leading (heven.pow_pos hne) s
    (schurExp_entry_sub_leading_isBigO L s i j hij)

omit [DecidableEq V] in
/-- Finite edge-count maximality upgrades edge inclusion to graph equality. -/
theorem graph_eq_of_le_of_card_le (G H : SimpleGraph V) (hle : G ≤ H)
    (hcard : H.edgeFinset.card ≤ G.edgeFinset.card) : G = H := by
  apply eq_of_le_of_not_lt hle
  intro hlt
  exact (not_lt_of_ge hcard) (Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt))

/-- Near zero the even Schur curve is admissible and retains every original
edge in both its numerical and logarithmic support, with positive log entries. -/
theorem eventually_schurExp_admissible (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (offDiagonalSupport L hL).Connected) (s : ℕ) (hs : 0 < s) (heven : Even s) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      (schurExp L s t).PosDef ∧
      (offDiagonalSupport (schurExp L s t) (schurExp_isHermitian L hL s t)).Connected ∧
      (∀ i j, 0 ≤ schurExp L s t i j) ∧
      (∀ i j, (offDiagonalSupport L hL).Adj i j →
        0 < EntropyCompletion.matrixLog (schurExp L s t) i j) := by
  letI : Nonempty V := hG.nonempty
  have he (i j : V) : ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      (offDiagonalSupport L hL).Adj i j →
        0 < schurExp L s t i j ∧ 0 < EntropyCompletion.matrixLog (schurExp L s t) i j := by
    by_cases hij : (offDiagonalSupport L hL).Adj i j
    · exact ((eventually_schurExp_entry_pos L s heven i j hij.1 hij.2).and
        (eventually_matrixLog_schurExp_entry_pos L hL s hs heven i j hij.1 hij.2)).mono
        (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hij h).elim)
  have hp : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (schurExp L s t).PosDef :=
    (eventually_posDef_schurExp L hL s hs).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, eventually_all.mpr (fun i => eventually_all.mpr (he i))] with t ht hedges
  refine ⟨ht, ?_, ?_, ?_⟩
  · apply hG.mono
    intro i j hij
    exact ⟨hij.1, ne_of_gt (hedges i j hij).1⟩
  · intro i j
    exact heven.pow_nonneg _
  · intro i j hij
    exact (hedges i j hij).2

/-- An eventual rational maximum-edge bound gives exact preservation of
logarithmic support and positivity of all its edges for every sufficiently
small positive rational parameter. This is the support premise needed by 4.3. -/
theorem rational_schur_logSupport_eq_of_maximal
    (L : Matrix V V ℝ) (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (s : ℕ) (hs : 0 < s) (heven : Even s)
    (hmax : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
      (schurExp L s q).PosDef →
      (offDiagonalSupport (schurExp L s q) (schurExp_isHermitian L hL s q)).Connected →
      (∀ i j, 0 ≤ schurExp L s q i j) →
      (logSupport (schurExp L s q)).edgeFinset.card ≤ (offDiagonalSupport L hL).edgeFinset.card) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < δ →
      (schurExp L s q).PosDef ∧ logSupport (schurExp L s q) = offDiagonalSupport L hL ∧
      ∀ i j, (logSupport (schurExp L s q)).Adj i j →
        0 < EntropyCompletion.matrixLog (schurExp L s q) i j := by
  obtain ⟨ε, hε, hmax⟩ := hmax
  have he := eventually_nhdsWithin_iff.mp (eventually_schurExp_admissible L hL hG s hs heven)
  obtain ⟨ζ, hζ, hz⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε ζ, lt_min hε hζ, ?_⟩
  intro q hq hqδ
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : dist (q : ℝ) 0 < ζ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hqr] using (lt_min_iff.mp hqδ).2
  obtain ⟨hpd, hc, hn, hlog⟩ := hz hd hqr
  have hle : offDiagonalSupport L hL ≤ logSupport (schurExp L s q) :=
    fun i j hij => ⟨hij.1, ne_of_gt (hlog i j hij)⟩
  have heq := (graph_eq_of_le_of_card_le _ _ hle
    (hmax q hq (lt_min_iff.mp hqδ).1 hpd hc hn)).symm
  refine ⟨hpd, heq, ?_⟩
  intro i j hij
  exact hlog i j (heq ▸ hij)

/-- The maximum logarithmic edge count is attained in any nonempty matrix family,
even when the matrix family itself is infinite. -/
theorem exists_maximal_logSupport (C : Set (Matrix V V ℝ)) (hC : C.Nonempty) :
    ∃ M ∈ C, ∀ H ∈ C, (logSupport H).edgeFinset.card ≤ (logSupport M).edgeFinset.card := by
  obtain ⟨G, ⟨M, hM, rfl⟩, hmax⟩ := Set.exists_max_image (logSupport '' C)
    (fun G : SimpleGraph V => G.edgeFinset.card) (Set.toFinite _) (hC.image logSupport)
  exact ⟨M, hM, fun H hH => hmax (logSupport H) ⟨H, hH, rfl⟩⟩

end PlanarHom.MaximumLogarithmicSupport
