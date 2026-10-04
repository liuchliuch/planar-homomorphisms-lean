import PlanarHom.UniformMatrixPowerRestriction
import PlanarHom.DomainSpectralAppendReduction

/-! The uniform power-family simulator with exact intrinsic domain metadata.
Old domains are retained and each private path vertex receives the allowed
full-domain record. Path typing is checked against the original source policy. -/
noncomputable section
namespace PlanarHom.UniformDomainPowerSimulation
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut dt : ℕ}

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full = Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y) :
    PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem basis M (extendedUnaries U D) (fun _ => 1)
        (fun n => M old ^ n) (EncodedGraph (appendOne B (B old)) T))
      (domainEvaluationProblem basis M U (fun _ => 1) D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  let transform : ℕ → MixedCode → MixedCode :=
    fun n g => g.stretchLabelDomainsLength bt old.val (ut+full.val) n
  have validT : ∀ g, HT g → g.Valid (bt+1) (ut+dt) := fun _ h => (h.planarValid _ T).1
  have validS : ∀ g, HS g → g.Valid bt (ut+dt) := fun _ h => (h.planarValid B T).1
  have hq : ∀ g, HT g → ∀ n, 1 ≤ n → HS (transform n g) := by
    intro g hg n _
    exact hg.stretchAppendedAuxiliary old full hpath (n-1)
  have hcorrect : ∀ g (hg : HT g) n (hn : 1 ≤ n),
      (transform n g).evaluate (validS _ (hq g hg n hn)) M (extendedUnaries U D) (fun _ => 1) =
        g.evaluate (validT g hg) (appendOne M (M old ^ n)) (extendedUnaries U D) (fun _ => 1) := by
    intro g hg n hn
    have hf := (g.stretchLabelLength bt old.val n).evaluate_withFreshDomains
      (g.stretchLabelLength_valid (validT g hg) bt n old (g.appended_companion_bound (validT g hg)))
      g.vertices (Fin.natAdd ut full) M (extendedUnaries U D) (fun _ => 1)
      (extendedUnaries_full U D full hfull)
    have he := g.evaluate_stretchLabelLength_appendOne (validT g hg) old n hn M (extendedUnaries U D)
    have hde : Classical.decEq (Fin q) = instDecidableEqFin q := Subsingleton.elim _ _
    simpa only [hde] using hf.trans he
  let r := UniformMatrixPowerRestriction.reductionOn basis M (extendedUnaries U D) old HT HS
    validT validS transform (fp_stretchLabelDomainsLength bt old.val (ut+full.val)) hq hcorrect
  exact r.transport _ _ (fun _ h => h)
    (fun raw h => (encodedInput_iff_graph B T raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

end PlanarHom.UniformDomainPowerSimulation
