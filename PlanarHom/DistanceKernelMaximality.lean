import PlanarHom.MaximumSupportLocalGeometry
import PlanarHom.DistanceKernelLog
import PlanarHom.MatrixLogContinuity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Distance-kernel sparsity from rational maximality

Local continuity of the actual spectral logarithm extends rational nonedge zeros
to all small positive real parameters. Thus the conditional chapter-four core
requires only three explicit rational candidate edge-count bounds, not an
assumed real-parameter analytic sparsity statement.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter
namespace PlanarHom.MaximumLogarithmicSupport
open LogarithmicSupport MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The eventual numerical bound for rational graph-distance-kernel candidates. -/
def RationalDistanceKernelEdgeBound (G : SimpleGraph V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < ε →
    (EntropyCompletion.distanceKernel G q).PosDef →
    (∀ i j, 0 < EntropyCompletion.distanceKernel G q i j) →
    (logSupport (EntropyCompletion.distanceKernel G q)).edgeFinset.card ≤ G.edgeFinset.card

/-- Rational candidate maximality and genuine first-order edge persistence give
exact logarithmic support at every sufficiently small positive rational parameter. -/
theorem rational_distanceKernel_logSupport_eq (G : SimpleGraph V) (hc : G.Connected)
    (hmax : RationalDistanceKernelEdgeBound G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < δ →
      logSupport (EntropyCompletion.distanceKernel G q) = G := by
  letI : Nonempty V := hc.nonempty
  obtain ⟨ε, hε, hmax⟩ := hmax
  have he (i j : V) : ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      G.Adj i j → 0 < EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G t) i j := by
    by_cases hij : G.Adj i j
    · exact (eventually_matrixLog_distanceKernel_edge_pos G hc i j hij).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hij h).elim)
  have hp : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (EntropyCompletion.distanceKernel G t).PosDef :=
    (EntropyCompletion.eventually_posDef_distanceKernel G hc).filter_mono nhdsWithin_le_nhds
  have hall := hp.and (eventually_all.mpr (fun i => eventually_all.mpr (he i)))
  obtain ⟨ζ, hζ, hz⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hall)
  refine ⟨min ε ζ, lt_min hε hζ, ?_⟩
  intro q hq hqδ
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : dist (q : ℝ) 0 < ζ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hqr] using (lt_min_iff.mp hqδ).2
  obtain ⟨hpd, hlog⟩ := hz hd hqr
  have hle : G ≤ logSupport (EntropyCompletion.distanceKernel G q) :=
    fun i j hij => ⟨hij.ne, ne_of_gt (hlog i j hij)⟩
  apply (graph_eq_of_le_of_card_le _ _ hle ?_).symm
  exact hmax q hq (lt_min_iff.mp hqδ).1 hpd (fun i j => pow_pos hqr _)

/-- Continuity on an open real interval extends rational zeros to every point. -/
theorem continuousOn_zero_of_positive_rat_zero {f : ℝ → ℝ} {ε : ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 ε))
    (hrat : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε → f q = 0)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 ε) : f x = 0 := by
  obtain ⟨u, _, hu, hut⟩ := Real.exists_seq_rat_strictMono_tendsto x
  have hfx : Tendsto (fun n => f (u n : ℝ)) atTop (𝓝 (f x)) :=
    (hf.continuousAt (Ioo_mem_nhds hx.1 hx.2)).tendsto.comp hut
  have he : (fun n => f (u n : ℝ)) =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [hut.eventually (Ioi_mem_nhds hx.1)] with n hn
    exact hrat (u n) hn ((hu n).trans hx.2)
  exact tendsto_nhds_unique_of_eventuallyEq hfx tendsto_const_nhds he

/-- The full real initial logarithmic-sparsity statement is derived from the
rational candidate edge-count bound and proved local log continuity. -/
theorem initiallyLogSparse_of_rational_distanceKernel_maximality
    (G : SimpleGraph V) (hc : G.Connected) (hmax : RationalDistanceKernelEdgeBound G) :
    EntropyCompletion.initiallyLogSparse G := by
  letI : Nonempty V := hc.nonempty
  obtain ⟨δ, hδ, hrat⟩ := rational_distanceKernel_logSupport_eq G hc hmax
  let Q : ℝ → Matrix V V ℝ := fun t => EntropyCompletion.distanceKernel G t - 1
  have hQ : Continuous Q := (EntropyCompletion.continuous_distanceKernel G).sub continuous_const
  have hH : ∀ t, (Q t).IsHermitian := fun t =>
    (EntropyCompletion.distanceKernel_isHermitian G t).sub Matrix.isHermitian_one
  have hzero : Q 0 = 0 := by simp [Q, EntropyCompletion.distanceKernel_zero G hc]
  obtain ⟨ζ, hζ, hcont⟩ := MatrixLogContinuity.exists_pos_continuousOn_matrixLog_one_add_comp Q hQ hH hzero
  have heq : ∀ t, 1 + Q t = EntropyCompletion.distanceKernel G t := by intro t; dsimp [Q]; abel
  have hcont' : ContinuousOn (fun t => EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G t))
      (Set.Ioo 0 (min δ ζ)) := by
    simpa only [heq] using hcont.mono (show Set.Ioo 0 (min δ ζ) ⊆ Set.Ioo (-ζ) ζ by
      intro t ht
      exact ⟨by linarith [ht.1], (lt_min_iff.mp ht.2).2⟩)
  refine ⟨min δ ζ, lt_min hδ hζ, ?_⟩
  intro x hx hxδ i j hij hn
  apply continuousOn_zero_of_positive_rat_zero
    ((KernelContinuation.entryCLM i j).continuous.comp_continuousOn hcont') _ ⟨hx, hxδ⟩
  intro q hq hqδ
  have he := hrat q (by exact_mod_cast hq) (lt_min_iff.mp hqδ).1
  by_contra hne
  have hedge : (logSupport (EntropyCompletion.distanceKernel G q)).Adj i j := ⟨hij, hne⟩
  exact hn (he ▸ hedge)

/-- The pure analytic/combinatorial chapter-four conclusion from three explicit
rational maximum-edge bounds. Their joint-availability justification is separate. -/
theorem cartesian_product_of_three_rational_bounds (L : Matrix V V ℝ)
    (hL : L.IsHermitian) (hG : (offDiagonalSupport L hL).Connected)
    (hpositive : ∀ i j, (offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (hschur : RationalSchurEdgeBound L hL)
    (hwheat : RationalWheatstoneEdgeBound (offDiagonalSupport L hL))
    (hkernel : RationalDistanceKernelEdgeBound (offDiagonalSupport L hL)) :
    ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
      Nonempty ((offDiagonalSupport L hL) ≃g CartesianGeometry.hammingGraph (fun i => Fin (s i))) :=
  cartesian_product_of_rational_maximality L hL hG hpositive hschur hwheat
    (initiallyLogSparse_of_rational_distanceKernel_maximality _ hG hkernel)

end PlanarHom.MaximumLogarithmicSupport
