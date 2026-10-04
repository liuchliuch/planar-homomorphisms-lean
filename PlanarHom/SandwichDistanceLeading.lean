import PlanarHom.SymmetricBCH
import PlanarHom.SparseExponentialLeading

/-!
# Graph-distance leading terms of a symmetric exponential sandwich

Each entry has a finite, continuous-in-slope leading coefficient at its graph
distance. At slope zero it is the positive exponential coefficient of the
outer matrix. Hence sufficiently small positive slopes produce entrywise
positive actual matrices for sufficiently small positive time.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A supported matrix exponential has a graph-distance expansion even if
some edge weights vanish or are negative. -/
theorem exp_supported_distance_leading_isBigO (G : SimpleGraph V) (hG : G.Connected)
    (M : Matrix V V ℝ) (hM : SupportedOn G M) (i j : V) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • M) i j -
      ((M ^ G.dist i j) i j / ((G.dist i j).factorial : ℝ)) * t ^ G.dist i j)
      =O[𝓝 0] (fun t : ℝ => t ^ (G.dist i j + 1)) := by
  have hs : ∀ᶠ (t : ℝ) in 𝓝 0, SupportedOn G (t • M) := Eventually.of_forall fun t i j hij hn => by
    simp [hM i j hij hn]
  have hd : ∀ i, (fun t : ℝ => (t • M) i i) =O[𝓝 0] (fun t : ℝ => t) := by
    intro i
    simpa only [Matrix.smul_apply, smul_eq_mul, mul_comm] using
      (isBigO_refl (fun t : ℝ => t) (𝓝 0)).const_mul_left (M i i)
  have he : ∀ i j, G.Adj i j →
      (fun t : ℝ => (t • M) i j - M i j * t ^ 1) =O[𝓝 0] (fun t : ℝ => t ^ (1 + 1)) := by
    intro i j hij
    simpa only [Matrix.smul_apply, smul_eq_mul, pow_one, mul_comm, sub_self] using
      (isBigO_zero (E' := ℝ) (fun t : ℝ => t ^ 2) (𝓝 0))
  simpa only [Nat.one_mul] using
    supported_exp_distance_leading_isBigO G hG (fun t => t • M) M 1 (by omega) hs hM hd he i j

end PlanarHom.MatrixLogCoefficients

namespace PlanarHom.SymmetricBCH
open MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite coefficient of one intermediate-color pair at shortest total degree. -/
def tripleDistanceCoefficient (G : SimpleGraph V) (C B : Matrix V V ℝ)
    (η : ℝ) (i u v j : V) : ℝ :=
  (((1 / 2 : ℝ) • C) ^ G.dist i u) i u / ((G.dist i u).factorial : ℝ) *
  ((η • B) ^ G.dist u v) u v / ((G.dist u v).factorial : ℝ) *
  (((1 / 2 : ℝ) • C) ^ G.dist v j) v j / ((G.dist v j).factorial : ℝ)

/-- The actual first possible coefficient of the sandwich entry. -/
def distanceCoefficient (G : SimpleGraph V) (C B : Matrix V V ℝ)
    (η : ℝ) (i j : V) : ℝ :=
  ∑ v, ∑ u, if G.dist i u + G.dist u v + G.dist v j = G.dist i j then
    tripleDistanceCoefficient G C B η i u v j else 0

/-- Explicit entry formula with both internal colors. -/
theorem sandwich_entry_sum (C B : Matrix V V ℝ) (t : ℝ) (i j : V) :
    sandwich C B t i j = ∑ v, ∑ u,
      NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C)) i u *
      NormedSpace.exp ℝ (t • B) u v *
      NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C)) v j := by
  simp only [sandwich, Matrix.mul_apply, Finset.sum_mul]

/-- The leading sandwich entry is derived from actual exponential expansions
and exact graph-distance inequalities. -/
theorem sandwich_distance_leading_isBigO (G : SimpleGraph V) (hG : G.Connected)
    (C B : Matrix V V ℝ) (hC : SupportedOn G C) (hB : SupportedOn G B)
    (η : ℝ) (i j : V) :
    (fun t => sandwich C (η • B) t i j - distanceCoefficient G C B η i j * t ^ G.dist i j)
      =O[𝓝 0] (fun t : ℝ => t ^ (G.dist i j + 1)) := by
  have hhalf : SupportedOn G ((1 / 2 : ℝ) • C) := by
    intro u v huv hn; simp [hC u v huv hn]
  have hηB : SupportedOn G (η • B) := by
    intro u v huv hn; simp [hB u v huv hn]
  have hterm : ∀ v u : V,
      (fun t =>
        NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C)) i u *
        NormedSpace.exp ℝ (t • (η • B)) u v *
        NormedSpace.exp ℝ (t • ((1 / 2 : ℝ) • C)) v j -
        (if G.dist i u + G.dist u v + G.dist v j = G.dist i j then
          tripleDistanceCoefficient G C B η i u v j else 0) * t ^ G.dist i j)
        =O[𝓝 0] (fun t : ℝ => t ^ (G.dist i j + 1)) := by
    intro v u
    let a := (((1 / 2 : ℝ) • C) ^ G.dist i u) i u / ((G.dist i u).factorial : ℝ)
    let b := ((η • B) ^ G.dist u v) u v / ((G.dist u v).factorial : ℝ)
    let c := (((1 / 2 : ℝ) • C) ^ G.dist v j) v j / ((G.dist v j).factorial : ℝ)
    have ha := exp_supported_distance_leading_isBigO G hG ((1 / 2 : ℝ) • C) hhalf i u
    have hb := exp_supported_distance_leading_isBigO G hG (η • B) hηB u v
    have hc := exp_supported_distance_leading_isBigO G hG ((1 / 2 : ℝ) • C) hhalf v j
    have hprod := mul_leading_isBigO (a * b) c (G.dist i u + G.dist u v) (G.dist v j)
      (mul_leading_isBigO a b (G.dist i u) (G.dist u v) ha hb) hc
    have heq : a * b * c = tripleDistanceCoefficient G C B η i u v j := by
      dsimp [a, b, c, tripleDistanceCoefficient]
      ring
    rw [heq] at hprod
    by_cases hdeg : G.dist i u + G.dist u v + G.dist v j = G.dist i j
    · simpa only [hdeg, ite_true] using hprod
    · have htri₁ := hG.dist_triangle (u := i) (v := u) (w := j)
      have htri₂ := hG.dist_triangle (u := u) (v := v) (w := j)
      have hlt : G.dist i j + 1 ≤ G.dist i u + G.dist u v + G.dist v j := by omega
      have horder := (isBigO_of_leading _ _ hprod).trans (pow_isBigO_pow hlt)
      simpa only [hdeg, ite_false, zero_mul, sub_zero] using horder
  have hsum := IsBigO.sum (s := Finset.univ) (fun v _ =>
    IsBigO.sum (s := Finset.univ) (fun u _ => hterm v u))
  convert hsum using 1
  funext t
  rw [sandwich_entry_sum]
  simp only [distanceCoefficient, Finset.sum_sub_distrib, Finset.sum_mul]

/-- The first possible coefficient is a continuous function of the slope. -/
theorem continuous_distanceCoefficient (G : SimpleGraph V) (C B : Matrix V V ℝ) (i j : V) :
    Continuous (fun η => distanceCoefficient G C B η i j) := by
  unfold distanceCoefficient
  apply continuous_finset_sum
  intro v hv
  apply continuous_finset_sum
  intro u hu
  by_cases hdeg : G.dist i u + G.dist u v + G.dist v j = G.dist i j
  · simp only [hdeg, ite_true, tripleDistanceCoefficient]
    fun_prop
  · simp only [hdeg, ite_false]
    exact continuous_const

/-- At slope zero the actual sandwich is precisely the outer exponential. -/
theorem sandwich_zero_middle (C B : Matrix V V ℝ) (t : ℝ) :
    sandwich C ((0 : ℝ) • B) t = NormedSpace.exp ℝ (t • C) := by
  simp only [sandwich, zero_smul, smul_zero, NormedSpace.exp_zero, mul_one]
  rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • ((1 / 2 : ℝ) • C)))]
  congr 1
  module

/-- Comparing actual leading coefficients identifies the slope-zero value. -/
theorem distanceCoefficient_zero (G : SimpleGraph V) (hG : G.Connected)
    (C B : Matrix V V ℝ) (hC : SupportedOn G C) (hB : SupportedOn G B) (i j : V) :
    distanceCoefficient G C B 0 i j = (C ^ G.dist i j) i j / ((G.dist i j).factorial : ℝ) := by
  have hleft := sandwich_distance_leading_isBigO G hG C B hC hB 0 i j
  simp only [sandwich_zero_middle] at hleft
  exact leading_coefficient_unique _ _ _ hleft
    (exp_supported_distance_leading_isBigO G hG C hC i j)

/-- Positive outer logarithmic edges yield an interval of slopes on which
all actual sandwich entries are eventually strictly positive. -/
theorem exists_pos_slopes_eventually_sandwich_pos
    (C B : Matrix V V ℝ) (hC : C.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hB : SupportedOn (LogarithmicSupport.offDiagonalSupport C hC) B) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ i j, 0 < sandwich C (η • B) t i j := by
  let G := LogarithmicSupport.offDiagonalSupport C hC
  have hCs : SupportedOn G C := by
    intro i j hij hn
    by_contra hne
    exact hn ⟨hij, hne⟩
  have hpos (i j : V) : 0 < distanceCoefficient G C B 0 i j := by
    rw [distanceCoefficient_zero G hG C B hCs hB]
    exact exp_distance_leading_coefficient_pos C hC hG hedge i j
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, ∀ i j, 0 < distanceCoefficient G C B η i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact ((continuous_distanceCoefficient G C B i j).tendsto (0 : ℝ)).eventually_const_lt (hpos i j)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  have hm : η ∈ Metric.ball (0 : ℝ) δ := by simpa [Real.dist_eq, abs_of_pos hη] using hηδ
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact eventually_pos_of_positive_leading (hball hm i j) (G.dist i j)
    (sandwich_distance_leading_isBigO G hG C B hCs hB η i j)

variable [Nonempty V]

/-- The true logarithm's linear sandwich coefficient has a quadratic error. -/
theorem matrixLog_sandwich_entry_sub_linear_isBigO (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (i j : V) :
    (fun t => EntropyCompletion.matrixLog (sandwich C B t) i j - (C + B) i j * t)
      =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hr := (entry_isBigO (matrixLog_sandwich_cubic_remainder_isBigO C B hC hB) i j).trans
    (pow_isBigO_pow (show 2 ≤ 4 by omega))
  have hc := ((isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 0)).const_mul_left
    (cubicCorrection C B i j)).trans (pow_isBigO_pow (show 2 ≤ 3 by omega))
  convert hr.add hc using 1
  funext t
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Small positive slopes retain every original graph edge as a positive
entry of the actual logarithm for sufficiently small positive time. -/
theorem exists_pos_slopes_eventually_log_edges_pos
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport C hC).Adj i j → 0 < C i j) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ i j,
        (LogarithmicSupport.offDiagonalSupport C hC).Adj i j →
          0 < EntropyCompletion.matrixLog (sandwich C (η • B) t) i j := by
  let G := LogarithmicSupport.offDiagonalSupport C hC
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, ∀ i j, G.Adj i j → 0 < C i j + η * B i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : G.Adj i j
    · have hh : Tendsto (fun η : ℝ => C i j + η * B i j) (𝓝 0) (𝓝 (C i j)) := by
        simpa using (continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)
      exact (hh.eventually_const_lt (hedge i j hij)).mono fun η h _ => h
    · exact Eventually.of_forall fun η h => (hij h).elim
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  have hm : η ∈ Metric.ball (0 : ℝ) δ := by simpa [Real.dist_eq, abs_of_pos hη] using hηδ
  have hηB : (η • B).IsHermitian := by
    change star (η • B) = η • B
    rw [star_smul, star_trivial]
    exact congrArg (fun A : Matrix V V ℝ => η • A) hB
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : G.Adj i j
  · have hf := matrixLog_sandwich_entry_sub_linear_isBigO C (η • B) hC hηB i j
    have hpos := eventually_pos_of_positive_leading (hball hm i j hij) 1
      (by simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_one, Nat.reduceAdd] using hf)
    exact hpos.mono fun t ht _ => ht
  · exact Eventually.of_forall fun t h => (hij h).elim

/-- The exact fixed-slope positive candidate region needed in Proposition4.8,
with actual matrix positivity and retained positive logarithmic edges. -/
theorem exists_pos_slopes_eventually_sandwich_and_log_edges_pos
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hBherm : B.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport C hC).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hB : SupportedOn (LogarithmicSupport.offDiagonalSupport C hC) B) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
        (∀ i j, 0 < sandwich C (η • B) t i j) ∧
        (∀ i j, (LogarithmicSupport.offDiagonalSupport C hC).Adj i j →
          0 < EntropyCompletion.matrixLog (sandwich C (η • B) t) i j) := by
  obtain ⟨δ₁, hδ₁, hraw⟩ := exists_pos_slopes_eventually_sandwich_pos C B hC hG hedge hB
  obtain ⟨δ₂, hδ₂, hlog⟩ := exists_pos_slopes_eventually_log_edges_pos C B hC hBherm hedge
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro η hη hηδ
  exact (hraw η hη (lt_min_iff.mp hηδ).1).and (hlog η hη (lt_min_iff.mp hηδ).2)

end PlanarHom.SymmetricBCH
