import PlanarHom.WheatstoneLog
import PlanarHom.LogarithmicSupport
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Strict logarithmic-support obstruction from Wheatstone gadgets

Adjacent common neighbors create a new logarithmic edge while retaining old
edges. The signature is PD and entrywise positive at arbitrarily small positive
rational parameters. Joint availability remains a separate obligation.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.WheatstoneCoefficients
open LogarithmicSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All old edges persist in the actual logarithmic support near zero. -/
theorem eventually_le_logSupport_wheatstone (G : SimpleGraph V) (hc : G.Connected) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, G ≤ logSupport (wheatstoneMatrix G t) := by
  have he (i j : V) : ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      G.Adj i j → 0 < EntropyCompletion.matrixLog (wheatstoneMatrix G t) i j := by
    by_cases hij : G.Adj i j
    · exact (eventually_matrixLog_wheatstone_edge_pos G hc hij).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ h => (hij h).elim)
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (he i))] with t ht
  intro i j hij
  exact ⟨hij.ne, ne_of_gt (ht i j hij)⟩

/-- Adjacent common neighbors make this inclusion strict. -/
theorem eventually_lt_logSupport_wheatstone (G : SimpleGraph V) (hc : G.Connected)
    {i j u v : V} (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v)
    (ha : G.Adj u v) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0, G < logSupport (wheatstoneMatrix G t) := by
  have hij : i ≠ j := by
    intro h
    rw [h, SimpleGraph.dist_self] at hd
    omega
  have hnij : ¬ G.Adj i j := by
    intro h
    have := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  filter_upwards [eventually_le_logSupport_wheatstone G hc,
    eventually_matrixLog_wheatstone_pos G hc hd huv hcommon ha] with t hle hpos
  refine lt_iff_le_not_ge.mpr ⟨hle, ?_⟩
  intro hback
  exact hnij (hback ⟨hij, ne_of_gt hpos⟩)

/-- Every sufficiently small positive real neighborhood contains a rational witness. -/
theorem exists_positive_rat_of_eventually {P : ℝ → Prop}
    (hP : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, P t) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < ε ∧ P q := by
  have hp := eventually_nhdsWithin_iff.mp hP
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hp
  obtain ⟨q, hq, hqδ⟩ := exists_rat_btwn (lt_min hε hδ)
  refine ⟨q, by exact_mod_cast hq, (lt_min_iff.mp hqδ).1, ?_⟩
  have hdist : dist (q : ℝ) 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hq] using (lt_min_iff.mp hqδ).2
  exact hb hdist hq

/-- A strict support obstruction at arbitrarily small positive rational parameters,
including actual PD and entrywise positivity of the candidate matrix. -/
theorem exists_rat_wheatstone_more_log_edges (G : SimpleGraph V) (hc : G.Connected)
    {i j u v : V} (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v)
    (ha : G.Adj u v) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < ε ∧ (wheatstoneMatrix G q).PosDef ∧
      (∀ a b, 0 < wheatstoneMatrix G q a b) ∧
      G.edgeFinset.card < (logSupport (wheatstoneMatrix G q)).edgeFinset.card := by
  have hpd : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (wheatstoneMatrix G t).PosDef :=
    (eventually_posDef_wheatstoneMatrix G hc).filter_mono nhdsWithin_le_nhds
  have hlt := eventually_lt_logSupport_wheatstone G hc hd huv hcommon ha
  obtain ⟨q, hq, hqε, hpq, hltq⟩ := exists_positive_rat_of_eventually (hpd.and hlt) hε
  refine ⟨q, hq, hqε, hpq, ?_, ?_⟩
  · exact wheatstoneMatrix_entry_pos G hc (by exact_mod_cast hq)
  · exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hltq)

/-- An eventual rational maximum-edge bound rules out adjacent common neighbors.
The availability proof establishing this bound is kept explicit and separate. -/
theorem nonadjacent_commonNeighbors_of_rational_log_edge_bound
    (G : SimpleGraph V) (hc : G.Connected) {i j u v : V}
    (hd : G.dist i j = 2) (huv : u ≠ v)
    (hcommon : ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v)
    (hmax : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
      (wheatstoneMatrix G q).PosDef → (∀ a b, 0 < wheatstoneMatrix G q a b) →
      (logSupport (wheatstoneMatrix G q)).edgeFinset.card ≤ G.edgeFinset.card) :
    ¬ G.Adj u v := by
  intro ha
  obtain ⟨ε, hε, hmax⟩ := hmax
  obtain ⟨q, hq, hqε, hpd, hpos, hlt⟩ := exists_rat_wheatstone_more_log_edges G hc hd huv hcommon ha hε
  exact (not_le_of_gt hlt) (hmax q hq hqε hpd hpos)

end PlanarHom.WheatstoneCoefficients
