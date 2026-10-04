import PlanarHom.WeightedSpectralAppendReduction
import PlanarHom.PrescribedDomainStretch
import PlanarHom.PromiseReductionTransport

/-! Weighted spectral interpolation preserves original prescribed domains and
adds only the already permitted full-color domain to private path vertices. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
open PlanarHom.MatrixFamilyInterpolationMachines PlanarHom.PreparedSpectralRecovery
open PlanarHom.PrescribedDomains PlanarHom.ProductInterpolationPreparationMachines
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q bt ut dt t dimension : ℕ}

def domainWeightedSpectralAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hpath : ∀ x y,B old x y→PathDomainTyping B old full x y)
    (P : Fin t→Matrix (Fin q) (Fin q) K) (a b : Fin t→K)
    (hchains : ∀ n : ℕ,0<n→weightedChain (M old) w n=∑i,a i^n • P i)
    (hzero : ∀i,a i=0→b i=0) (hcompat : Compatible a b) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (∑i,b i • P i)) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U w D B T) := by
  let transform : ℕ→MixedCode→MixedCode := fun h g=>g.stretchLabelDomainsLength bt old.val (ut+full.val) h
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  have validT : ∀g,HT g→g.Valid (bt+1) (ut+dt) := fun _ h=>(h.planarValid _ T).1
  have validS : ∀g,HS g→g.Valid bt (ut+dt) := fun _ h=>(h.planarValid B T).1
  have hquery : ∀g,HT g→∀n,1≤n→HS (transform n g) := by
    intro g hg n _
    exact hg.stretchAppendedAuxiliary old full hpath (n-1)
  have hcorrect : ∀g (hg : HT g),
      recoverContext a ((preparation a b bt transform g).1,
        (preparation a b bt transform g).2.map (totalEvaluation M (extendedUnaries U D) w)) =
      g.evaluate (validT g hg) (appendOne M (∑i,b i • P i)) (extendedUnaries U D) w := by
    intro g hg
    have hq : ∀n,1≤n→totalEvaluation M (extendedUnaries U D) w (transform n g)=
        g.evaluate (validT g hg)
          (spectralLabels (appendOne M (M old)) (Fin.last bt) P (fun i=>a i^n))
          (extendedUnaries U D) w := by
      intro n hn
      rw [totalEvaluation_valid _ _ _ _ (validS _ (hquery g hg n hn))]
      have hf := (g.stretchLabelLength bt old.val n).evaluate_withFreshDomains
        (g.stretchLabelLength_valid (validT g hg) bt n old (g.appended_companion_bound (validT g hg)))
        g.vertices (Fin.natAdd ut full) M (extendedUnaries U D) w (extendedUnaries_full U D full hfull)
      have he := g.evaluate_stretchLabelLength_weighted (validT g hg) old n M (extendedUnaries U D) w
      have h := hf.trans he
      rw [hchains n (by omega)] at h
      have hl := replace_last_appendOne M (M old) (∑i,a i^n • P i)
      simpa only [←hl] using h
    have h := preparation_recovery_of_spectral_queries g (validT g hg) (Fin.last bt)
      (appendOne M (M old)) (extendedUnaries U D) w P a b hzero hcompat
      transform (totalEvaluation M (extendedUnaries U D) w) hq
    have hl : spectralLabels (appendOne M (M old)) (Fin.last bt) P b=appendOne M (∑i,b i • P i) :=
      replace_last_appendOne M (M old) _
    rw [hl] at h
    exact h
  let r := MatrixFamilyInterpolationMachines.reductionOn basis a b bt transform
    (fp_stretchLabelDomainsLength bt old.val (ut+full.val))
    (appendOne M (∑i,b i • P i)) (extendedUnaries U D) w
    M (extendedUnaries U D) w HT HS validT validS hquery hcorrect
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.Complexity.MixedCode
