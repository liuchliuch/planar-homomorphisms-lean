import PlanarHom.SpectralAppendReduction
import PlanarHom.TypedBipartiteSpectralPaths
import PlanarHom.HeterogeneousGraphReduction
import PlanarHom.PrescribedDomainStretch
import PlanarHom.PromiseReductionTransport

/-! Genuine spectral interpolation with a private prescribed subdomain.
Only the selected matrix is supported on the private side. All companion
matrices and all original prescribed-domain metadata remain unchanged. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
open PlanarHom.MatrixFamilyInterpolationMachines PlanarHom.PreparedSpectralRecovery
open PlanarHom.PrescribedDomains PlanarHom.ProductInterpolationPreparationMachines
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {C : Type} [Fintype C] [DecidableEq C]
variable {bt ut dt t dimension : ℕ}

/-- Joint spectral interpolation on the exact encoded prescribed-domain promise.
The four path endpoint cases are checked against the original source table. -/
def supportedSpectralAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hsupport : ∀ c, c ∉ D full → ∀ d, M old c d=0)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (P : Fin t → Matrix C C K) (a b : Fin t → K)
    (hpowers : ∀ n : ℕ, 0<n → M old ^ n = ∑ i, a i ^ n • P i)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (∑ i, b i • P i)) U (fun _ => 1)
        D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U (fun _ => 1) D B T) := by
  let transform : ℕ → MixedCode → MixedCode :=
    fun h g => g.stretchLabelDomainsLength bt old.val (ut+full.val) h
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  have validT : ∀ g, HT g → g.Valid (bt+1) (ut+dt) :=
    fun _ h => (h.planarValid _ T).1
  have validS : ∀ g, HS g → g.Valid bt (ut+dt) :=
    fun _ h => (h.planarValid B T).1
  have hquery : ∀ g, HT g → ∀ n, 1 ≤ n → HS (transform n g) := by
    intro g hg n _
    exact hg.stretchAppendedAuxiliary old full hpath (n-1)
  have hcorrect : ∀ g (hg : HT g),
      recoverContext a ((preparation a b bt transform g).1,
        (preparation a b bt transform g).2.map (totalEvaluation M (extendedUnaries U D) (fun _ => 1))) =
      g.evaluate (validT g hg) (appendOne M (∑ i, b i • P i)) (extendedUnaries U D) (fun _ => 1) := by
    intro g hg
    have hq : ∀ n, 1≤n → totalEvaluation M (extendedUnaries U D) (fun _ => (1 : K)) (transform n g) =
        g.evaluate (validT g hg)
          (fun l => if l=Fin.last bt then M old ^ n else appendOne M (M old) l)
          (extendedUnaries U D) (fun _ => 1) := by
      intro n hn
      rw [replace_last_appendOne]
      rw [totalEvaluation_valid M (extendedUnaries U D) (fun _ => 1) _
        (validS _ (hquery g hg n hn))]
      have hs : ∀ c d, M old c d ≠ 0 → extendedUnaries U D (Fin.natAdd ut full) c=1 := by
        intro c d hne
        have hc : c∈D full := by
          by_contra h
          exact hne (hsupport c h d)
        simp only [extendedUnaries,Fin.addCases_right,indicator,if_pos hc]
      have hf := g.evaluate_stretchLabel_withFreshDomains_of_support (validT g hg)
        bt (n-1) old (g.appended_companion_bound (validT g hg))
        (Fin.natAdd ut full) M (extendedUnaries U D) (fun _ => 1) hs
      have he := g.evaluate_stretchLabelLength_appendOne (validT g hg) old n hn M (extendedUnaries U D)
      exact hf.trans he
    have h := preparation_recovery_of_matrix_power_queries g (validT g hg) (Fin.last bt)
      (appendOne M (M old)) (extendedUnaries U D) (fun _ => 1) P (M old) a b hpowers hzero hcompat
      transform (totalEvaluation M (extendedUnaries U D) (fun _ => 1)) hq
    have hlabels : spectralLabels (appendOne M (M old)) (Fin.last bt) P b =
        appendOne M (∑ i, b i • P i) := replace_last_appendOne M (M old) _
    rw [hlabels] at h
    exact h
  let r := reductionOfHeterogeneousPipeline basis (metadataEncoding basis a)
    (appendOne M (∑ i, b i • P i)) (extendedUnaries U D) (fun _ => 1)
    M (extendedUnaries U D) (fun _ => 1) HT HS validT validS
    (preparation a b bt transform) (recoverContext a)
    (fp_preparation basis a b bt transform (fp_stretchLabelDomainsLength bt old.val (ut+full.val)))
    (fp_recover_context basis a)
    (by
      intro g hg query hq
      obtain ⟨n,hn,_,rfl⟩ := query_mem hq
      exact hquery g hg n hn) hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun raw h => (encodedInput_iff_graph B T raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

end PlanarHom.TypedBipartiteSpectral
