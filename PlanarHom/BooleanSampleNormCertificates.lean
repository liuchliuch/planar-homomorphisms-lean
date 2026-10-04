import PlanarHom.BooleanTowerRealEvaluation

/-! Norm certificates at the literal rational samples emitted by the FP sampler.
These discharge the grouped recovery's unit conditions over the entire radical
algebra, including square and dependent radicands. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanSampleNormCertificates
open BooleanFieldTower BooleanFieldCollision BooleanEffectiveLengthSamples
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b:ℕ}

theorem sampled_difference_norm_ne_zero (c a w:Fin b→K) (d:Fin b→ℕ) (ell m:ℕ)
    (q:ℚ) (hq:q∈samples c a w d ell m) (k l:Fin b→ℕ)
    (hk:∀g,k g≤d g*m) (hl:∀g,l g≤d g*m)
    (hdiff:∃g,a g≠0 ∧ k g≠l g) :
    norm (radicands a w (algebraMap ℚ K q)) b
      (sub b (spectral c a w (algebraMap ℚ K q) (fun g=>d g*m) k)
        (spectral c a w (algebraMap ℚ K q) (fun g=>d g*m) l))≠0 := by
  let p:=BooleanEffectiveSampling.prepare b (prepare d ell m)
  have hc : BooleanNormSampleMachines.counts (b:=b) p=fun g=>d g*m := totals_prepare d ell m
  have h:=BooleanNormSampleCompleteness.candidate_norm_ne_zero c a w p q hq k l
    (by simpa only [hc] using hk) (by simpa only [hc] using hl) hdiff
  simpa only [hc,collision] using h

theorem sampled_node_norm_ne_zero (f:K→+*ℝ) (c a w:Fin b→K) (d:Fin b→ℕ) (ell m:ℕ)
    (q:ℚ) (hq:q∈samples c a w d ell m) (k:Fin b→ℕ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i))) :
    norm (radicands a w (algebraMap ℚ K q)) b
      (spectral c a w (algebraMap ℚ K q) (fun g=>d g*m) k)≠0 := by
  apply BooleanTowerRealEvaluation.norm_spectral_ne_zero f c a w _ _ k hp
  simpa using (samples_bounds c a w d ell m q hq).1

end PlanarHom.BooleanSampleNormCertificates
