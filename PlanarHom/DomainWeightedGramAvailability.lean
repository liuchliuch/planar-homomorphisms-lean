import PlanarHom.WeightedGramAvailability
import PlanarHom.DomainWeightedSpectralAppend
import PlanarHom.PrescribedDomainQueryPromises

/-! The weighted Gram gadget under the original prescribed-domain policy.
Only private path vertices receive the already allowed full domain. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases PrescribedDomains PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K]
variable {q bt ut dt dimension : ℕ}

def domainGramTransform (bt selected fullLabel p : ℕ) (g : MixedCode) : MixedCode :=
  (g.parallelLabel bt p).stretchLabelDomainsLength bt selected fullLabel 2

theorem fp_domainGramTransform (selected fullLabel p : ℕ) :
    FP MixedCode.encoding MixedCode.encoding (domainGramTransform bt selected fullLabel p) := by
  have hparallel := ((fp_const MixedCode.encoding BitEncoding.unaryNat p).pair (fp_id MixedCode.encoding)).comp
    (MixedParallelMachines.fp_parallelLabel bt)
  exact ((fp_const MixedCode.encoding BitEncoding.unaryNat 2).pair hparallel).comp
    (fp_stretchLabelDomainsLength bt selected fullLabel)

def domainGramAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hpath : ∀ x y,B old x y→PathDomainTyping B old full x y) (p : ℕ) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (gramCoreField (M old) w p)) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U w D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  let transform := domainGramTransform bt old.val (ut+full.val) p
  have validT : ∀g,HT g→g.Valid (bt+1) (ut+dt) := fun _ h=>(h.planarValid _ T).1
  have validS : ∀g,HS g→g.Valid bt (ut+dt) := fun _ h=>(h.planarValid B T).1
  have hp : ∀g,HT g→HS (transform g) := by
    intro g hg
    exact (hg.parallelLabel _ T bt p).stretchAppendedAuxiliary old full hpath 1
  have he : ∀g (hg : HT g),totalEvaluation M (extendedUnaries U D) w (transform g)=
      g.evaluate (validT g hg) (appendOne M (gramCoreField (M old) w p)) (extendedUnaries U D) w := by
    intro g hg
    rw [totalEvaluation_valid _ _ _ _ (validS _ (hp g hg))]
    have hv := parallelLabel_valid bt p (bt+1) (ut+dt) g (validT g hg)
    have hs := (g.parallelLabel bt p).stretchLabelLength_valid hv bt 2 old
      ((g.parallelLabel bt p).appended_companion_bound hv)
    have hf := ((g.parallelLabel bt p).stretchLabelLength bt old.val 2).evaluate_withFreshDomains hs
      g.vertices (Fin.natAdd ut full) M (extendedUnaries U D) w (extendedUnaries_full U D full hfull)
    have hgram := gramTransform_evaluate g (validT g hg) M (extendedUnaries U D) w old p
    change totalEvaluation M (extendedUnaries U D) w ((g.parallelLabel bt p).stretchLabelLength bt old.val 2)=_ at hgram
    rw [totalEvaluation_valid _ _ _ _ hs] at hgram
    exact hf.trans hgram
  have hpre : FP encoding (BitEncoding.bits.prod encoding.list) (fun g=>([],[transform g])) := by
    have hl := ((fp_domainGramTransform (bt:=bt) old.val (ut+full.val) p).pair
      (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  let r := reductionOfPipeline basis BitEncoding.bits
    (appendOne M (gramCoreField (M old) w p)) (extendedUnaries U D) w
    M (extendedUnaries U D) w HT HS validT validS
    (fun g=>([],[transform g])) (fun z : Bits×List K=>z.2.sum) hpre
    ((fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis))
    (by intro g hg query hq; obtain rfl := List.mem_singleton.mp hq; exact hp g hg)
    (by intro g hg; simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using he g hg)
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.PositiveWeightRemoval
