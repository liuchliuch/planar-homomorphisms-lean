import PlanarHom.SpectralAppendReduction
import PlanarHom.PrescribedDomainStretch
import PlanarHom.PromiseReductionTransport

/-! Actual prescribed-domain spectral interpolation. Queries preserve the
original intrinsic domain metadata and add one full-domain record at each new
path vertex. The source and target share the fixed domain and typing tables. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
open PlanarHom.MatrixFamilyInterpolationMachines PlanarHom.PreparedSpectralRecovery
open PlanarHom.PrescribedDomains PlanarHom.ProductInterpolationPreparationMachines
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q bt ut dt t dimension : ℕ}

/-- Joint spectral interpolation on the exact encoded prescribed-domain promise.
The four path endpoint cases are checked against the original source table. -/
def domainSpectralAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full = Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (P : Fin t → Matrix (Fin q) (Fin q) K) (a b : Fin t → K)
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
      have hf := (g.stretchLabelLength bt old.val n).evaluate_withFreshDomains
        (g.stretchLabelLength_valid (validT g hg) bt n old
          (g.appended_companion_bound (validT g hg)))
        g.vertices (Fin.natAdd ut full) M (extendedUnaries U D) (fun _ => 1)
        (extendedUnaries_full U D full hfull)
      have hde : Classical.decEq (Fin q) = instDecidableEqFin q := Subsingleton.elim _ _
      have he := g.evaluate_stretchLabelLength_appendOne (validT g hg) old n hn M (extendedUnaries U D)
      simpa only [hde] using hf.trans he
    have h := preparation_recovery_of_matrix_power_queries g (validT g hg) (Fin.last bt)
      (appendOne M (M old)) (extendedUnaries U D) (fun _ => 1) P (M old) a b hpowers hzero hcompat
      transform (totalEvaluation M (extendedUnaries U D) (fun _ => 1)) hq
    have hlabels : spectralLabels (appendOne M (M old)) (Fin.last bt) P b =
        appendOne M (∑ i, b i • P i) := replace_last_appendOne M (M old) _
    rw [hlabels] at h
    exact h
  let r := MatrixFamilyInterpolationMachines.reductionOn basis a b bt transform
    (fp_stretchLabelDomainsLength bt old.val (ut+full.val))
    (appendOne M (∑ i, b i • P i)) (extendedUnaries U D) (fun _ => 1)
    M (extendedUnaries U D) (fun _ => 1) HT HS validT validS hquery hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun raw h => (encodedInput_iff_graph B T raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The source's full-color endpoint type implies all four path cases. -/
theorem pathDomainTyping_of_full_endpoints
    (B : Fin bt → Fin dt → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (htype : ∀ x y, B old x y → x=full ∧ y=full) :
    ∀ x y, B old x y → PathDomainTyping B old full x y := by
  intro x y h
  obtain ⟨rfl,rfl⟩ := htype x y h
  exact ⟨h,h,h,h⟩

/-- Compose only after all actual original-alphabet path queries are verified. -/
def domainSpectralAppend_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full = Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (P : Fin t → Matrix (Fin q) (Fin q) K) (a b : Fin t → K)
    (hpowers : ∀ n : ℕ, 0<n → M old ^ n = ∑ i, a i ^ n • P i)
    (hzero : ∀ i, a i=0 → b i=0) (hcompat : Compatible a b)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U (fun _ => 1) D B T) base) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (∑ i, b i • P i)) U (fun _ => 1)
        D (appendOne B (B old)) T) base :=
  (domainSpectralAppendReduction basis M U D B T old full hfull hpath P a b hpowers hzero hcompat).trans available

end PlanarHom.Complexity.MixedCode
