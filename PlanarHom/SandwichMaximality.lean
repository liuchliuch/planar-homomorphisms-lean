import PlanarHom.SchurPerturbation
import PlanarHom.SandwichDistanceLeading
import PlanarHom.MaximumLogarithmicSupport

/-!
# Rational sandwich maximum-edge arguments

The actual sandwich and its Schur square are proved admissible near zero.
Explicit numerical bounds on rational candidates then force support containment
and preservation. Joint availability of these candidates is deliberately a
separate computational obligation, not an asserted conclusion here.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.SandwichMaximality
open MatrixLogCoefficients LogarithmicSupport SymmetricBCH MaximumLogarithmicSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Real scalar multiplication preserves Hermitian matrices. -/
theorem hermitian_smul (B : Matrix V V ℝ) (hB : B.IsHermitian) (η : ℝ) :
    (η • B).IsHermitian := by
  change star (η • B) = η • B
  rw [star_smul, star_trivial]
  exact congrArg (fun A : Matrix V V ℝ => η • A) hB

/-- The actual squared-entry sandwich candidate. -/
def squareSandwich (C B : Matrix V V ℝ) (η t : ℝ) : Matrix V V ℝ :=
  schurCurve (sandwich C (η • B)) 2 t

theorem squareSandwich_isHermitian (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (η t : ℝ) :
    (squareSandwich C B η t).IsHermitian :=
  schurCurve_isHermitian _ 2 t (sandwich_isHermitian C (η • B) hC (hermitian_smul B hB η) t)

/-- The raw Hermitian sandwich is PD near zero. -/
theorem eventually_posDef_sandwich (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (η : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (sandwich C (η • B) t).PosDef := by
  have hz := (sandwich_sub_one_isBigO C (η • B)).trans_tendsto tendsto_id
  have ht : Tendsto (sandwich C (η • B)) (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hz.add_const (1 : Matrix V V ℝ)
  exact eventually_posDef_of_tendsto_one _
    (Eventually.of_forall fun t => sandwich_isHermitian C (η • B) hC (hermitian_smul B hB η) t) ht

/-- The actual Schur-square sandwich is PD near zero without any assumed Schur closure. -/
theorem eventually_posDef_squareSandwich (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (η : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (squareSandwich C B η t).PosDef := by
  have hz := (schurCurve_sub_one_isBigO (sandwich C (η • B)) 2 (by omega)
    (sandwich_sub_one_isBigO C (η • B))).trans_tendsto tendsto_id
  have ht : Tendsto (squareSandwich C B η) (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hz.add_const (1 : Matrix V V ℝ)
  exact eventually_posDef_of_tendsto_one _
    (Eventually.of_forall fun t => squareSandwich_isHermitian C B hC hB η t) ht

/-- All original positive edge coefficients survive sufficiently small slopes. -/
theorem exists_pos_slopes_edge_coefficients_pos (C B : Matrix V V ℝ) (hC : C.IsHermitian)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j + η * B i j := by
  have he : ∀ᶠ η : ℝ in 𝓝 0, ∀ i j,
      (offDiagonalSupport C hC).Adj i j → 0 < C i j + η * B i j := by
    rw [eventually_all]; intro i
    rw [eventually_all]; intro j
    by_cases hij : (offDiagonalSupport C hC).Adj i j
    · have hh : Tendsto (fun η : ℝ => C i j + η * B i j) (𝓝 0) (𝓝 (C i j)) := by
        simpa using (continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)
      exact (hh.eventually_const_lt (hedge i j hij)).mono fun η ht _ => ht
    · exact Eventually.of_forall fun η ht => (hij ht).elim
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  exact hball (by simpa [Real.dist_eq, abs_of_pos hη] using hηδ)

/-- The square candidate is admissible and keeps every old logarithmic edge. -/
theorem eventually_squareSandwich_admissible (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (hG : (offDiagonalSupport C hC).Connected)
    (η : ℝ) (hcoeff : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j + η * B i j) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      (squareSandwich C B η t).PosDef ∧
      (offDiagonalSupport (squareSandwich C B η t) (squareSandwich_isHermitian C B hC hB η t)).Connected ∧
      (∀ i j, 0 ≤ squareSandwich C B η t i j) ∧
      (∀ i j, (offDiagonalSupport C hC).Adj i j →
        0 < EntropyCompletion.matrixLog (squareSandwich C B η t) i j) := by
  letI : Nonempty V := hG.nonempty
  have he (i j : V) : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (offDiagonalSupport C hC).Adj i j →
      0 < squareSandwich C B η t i j ∧
      0 < EntropyCompletion.matrixLog (squareSandwich C B η t) i j := by
    by_cases hij : (offDiagonalSupport C hC).Adj i j
    · have hf := sandwich_entry_sub_linear_isBigO C (η • B) i j hij.1
      have hraw := eventually_pos_of_positive_leading (hcoeff i j hij) 1
        (by simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_one, Nat.reduceAdd] using hf)
      have hlog := eventually_matrixLog_schur_square_sandwich_entry_pos C B hC hB η i j hij.1
        (ne_of_gt (hcoeff i j hij))
      filter_upwards [hraw, hlog] with t ht hl h
      exact ⟨sq_pos_of_pos ht, hl⟩
    · exact Eventually.of_forall fun t h => (hij h).elim
  have hp : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (squareSandwich C B η t).PosDef :=
    (eventually_posDef_squareSandwich C B hC hB η).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, eventually_all.mpr (fun i => eventually_all.mpr (he i))] with t hpd he
  refine ⟨hpd, ?_, fun i j => sq_nonneg _, fun i j hij => (he i j hij).2⟩
  apply hG.mono
  intro i j hij
  exact ⟨hij.1, ne_of_gt (he i j hij).1⟩

/-- Explicit rational-candidate edge bounds for the support-containment step. -/
def RationalSquareSandwichEdgeBound (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) : Prop :=
  ∀ η : ℚ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
    (squareSandwich C B η q).PosDef →
    (offDiagonalSupport (squareSandwich C B η q) (squareSandwich_isHermitian C B hC hB η q)).Connected →
    (∀ i j, 0 ≤ squareSandwich C B η q i j) →
    (logSupport (squareSandwich C B η q)).edgeFinset.card ≤ (offDiagonalSupport C hC).edgeFinset.card

/-- A new off-diagonal entry of B would create an extra logarithmic edge in
an actual small positive rational square sandwich, contradicting the numerical bound. -/
theorem supportedOn_of_rational_squareSandwich_maximality (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (hG : (offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hmax : RationalSquareSandwichEdgeBound C B hC hB) :
    SupportedOn (offDiagonalSupport C hC) B := by
  letI : Nonempty V := hG.nonempty
  intro i j hij hnot
  by_contra hne
  have hCij : C i j = 0 := by
    by_contra hc
    exact hnot ⟨hij, hc⟩
  obtain ⟨δ, hδ, hcoeff⟩ := exists_pos_slopes_edge_coefficients_pos C B hC hedge
  obtain ⟨η, hη, hηδ⟩ := exists_rat_btwn hδ
  have hηrat : 0 < η := by exact_mod_cast hη
  have hcoef := hcoeff (η : ℝ) hη hηδ
  obtain ⟨ε, hε, hmaxη⟩ := hmax η hηrat
  have hadm := eventually_squareSandwich_admissible C B hC hB hG (η : ℝ) hcoef
  have hextra := eventually_matrixLog_schur_square_sandwich_entry_pos C B hC hB (η : ℝ) i j hij
    (by rw [hCij, zero_add]; exact mul_ne_zero (ne_of_gt hη) hne)
  have he := eventually_nhdsWithin_iff.mp (hadm.and hextra)
  obtain ⟨ζ, hζ, hz⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨q, hq, hqbound⟩ := exists_rat_btwn (lt_min hε hζ)
  have hqrat : 0 < q := by exact_mod_cast hq
  have hd : dist (q : ℝ) 0 < ζ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hq] using (lt_min_iff.mp hqbound).2
  obtain ⟨⟨hpd, hc, hn, hl⟩, hex⟩ := hz hd hq
  have hle : offDiagonalSupport C hC ≤ logSupport (squareSandwich C B η q) :=
    fun a b hab => ⟨hab.1, ne_of_gt (hl a b hab)⟩
  have heq := graph_eq_of_le_of_card_le _ _ hle
    (hmaxη q hqrat (lt_min_iff.mp hqbound).1 hpd hc hn)
  have hedgeNew : (logSupport (squareSandwich C B η q)).Adj i j := ⟨hij, ne_of_gt hex⟩
  exact hnot (heq.symm ▸ hedgeNew)

/-- Explicit rational-candidate edge bound for the raw sandwich after support containment. -/
def RationalSandwichEdgeBound (C B : Matrix V V ℝ) (hC : C.IsHermitian) : Prop :=
  ∀ η : ℚ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
    (sandwich C ((η : ℝ) • B) q).PosDef →
    (∀ i j, 0 < sandwich C ((η : ℝ) • B) q i j) →
    (logSupport (sandwich C ((η : ℝ) • B) q)).edgeFinset.card ≤ (offDiagonalSupport C hC).edgeFinset.card

/-- On every sufficiently small positive rational slope ray, numerical
maximality forces the raw sandwich log to have exactly the original support. -/
theorem rational_sandwich_logSupport_eq_of_maximal
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hG : (offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hsupport : SupportedOn (offDiagonalSupport C hC) B)
    (hmax : RationalSandwichEdgeBound C B hC) :
    ∃ δ > 0, ∀ η : ℚ, 0 < η → (η : ℝ) < δ →
      ∃ ε > 0, ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
        (sandwich C ((η : ℝ) • B) q).PosDef ∧
        (∀ i j, 0 < sandwich C ((η : ℝ) • B) q i j) ∧
        logSupport (sandwich C ((η : ℝ) • B) q) = offDiagonalSupport C hC ∧
        (∀ i j, (offDiagonalSupport C hC).Adj i j →
          0 < EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) q) i j) := by
  letI : Nonempty V := hG.nonempty
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_slopes_eventually_sandwich_and_log_edges_pos
    C B hC hB hG hedge hsupport
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨ε, hε, hbound⟩ := hmax η hη
  have hp : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (sandwich C ((η : ℝ) • B) t).PosDef :=
    (eventually_posDef_sandwich C B hC hB η).filter_mono nhdsWithin_le_nhds
  have he := eventually_nhdsWithin_iff.mp (hp.and (hpos (η : ℝ) hηreal hηδ))
  obtain ⟨ζ, hζ, hz⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε ζ, lt_min hε hζ, ?_⟩
  intro q hq hqδ
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : dist (q : ℝ) 0 < ζ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hqreal] using (lt_min_iff.mp hqδ).2
  obtain ⟨hpd, hentry, hlog⟩ := hz hd hqreal
  have hle : offDiagonalSupport C hC ≤ logSupport (sandwich C ((η : ℝ) • B) q) :=
    fun i j hij => ⟨hij.1, ne_of_gt (hlog i j hij)⟩
  have heq := graph_eq_of_le_of_card_le _ _ hle
    (hbound q hq (lt_min_iff.mp hqδ).1 hpd hentry)
  exact ⟨hpd, hentry, heq.symm, hlog⟩

/-- Combining the two explicit candidate bounds derives both source support
containment and rational raw-log support preservation. -/
theorem support_and_rational_logSupport_of_sandwich_maximality
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hG : (offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hsquare : RationalSquareSandwichEdgeBound C B hC hB)
    (hraw : RationalSandwichEdgeBound C B hC) :
    SupportedOn (offDiagonalSupport C hC) B ∧
      ∃ δ > 0, ∀ η : ℚ, 0 < η → (η : ℝ) < δ →
        ∃ ε > 0, ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
          logSupport (sandwich C ((η : ℝ) • B) q) = offDiagonalSupport C hC := by
  have hs := supportedOn_of_rational_squareSandwich_maximality C B hC hB hG hedge hsquare
  obtain ⟨δ, hδ, hr⟩ := rational_sandwich_logSupport_eq_of_maximal C B hC hB hG hedge hs hraw
  refine ⟨hs, δ, hδ, ?_⟩
  intro η hη hηδ
  obtain ⟨ε, hε, he⟩ := hr η hη hηδ
  exact ⟨ε, hε, fun q hq hqε => (he q hq hqε).2.2.1⟩

end PlanarHom.SandwichMaximality
