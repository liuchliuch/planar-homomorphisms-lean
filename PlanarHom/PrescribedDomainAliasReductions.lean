import PlanarHom.PrescribedDomainAliases
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.MixedLabelAliasReductions
import PlanarHom.PromiseReductionTransport

/-! # Actual raw-code label aliases preserving exact prescribed-domain typing -/
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLabelLookupMachines
variable {a b d bt ut : ℕ}

theorem EncodedGraph.relabelBinaryAlias (ρ : Fin a→Fin b)
    {BT : Fin a→Fin d→Fin d→Prop} {BS : Fin b→Fin d→Fin d→Prop} {U : Fin ut→Fin d→Prop}
    (hB : ∀i x y,BT i x y→BS (ρ i) x y) {g : MixedCode} (h : EncodedGraph BT U g) :
    EncodedGraph BS U (g.relabelBinary (finTable ρ)) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=ut) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [relabelBinary_withDomains]
  apply encodedInput_encode_withDomains (ht.relabelBinaryAlias ρ hB)
  simpa only [relabelBinary_underlying] using hp

theorem EncodedGraph.relabelUnaryAlias (ρ : Fin a→Fin b)
    {B : Fin bt→Fin d→Fin d→Prop} {UT : Fin a→Fin d→Prop} {US : Fin b→Fin d→Prop}
    (hU : ∀i x,UT i x→US (ρ i) x) {g : MixedCode} (h : EncodedGraph B UT g) :
    EncodedGraph B US (g.relabelUnary (finTable (liftUnaryAlias ρ d))) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=a) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [relabelUnary_withDomains ρ original hg δ]
  exact encodedInput_encode_withDomains (ht.relabelUnaryAlias ρ hU) hp

end PlanarHom.PrescribedDomains

namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.PrescribedDomains PlanarHom.FiniteLabelLookupMachines PlanarHom.FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension a b ut bt d : ℕ}

/-- Actual binary-label alias reduction on arbitrary successfully decoded domain
inputs, preserving the original δ, every unary companion, and all endpoints. -/
noncomputable def domainBinaryRelabelReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→Fin b) (M : Fin b→Matrix C C K) (U : Fin ut→C→K) (w : C→K) (D : Fin d→Set C)
    (BT : Fin a→Fin d→Fin d→Prop) (BS : Fin b→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (hB : ∀i x y,BT i x y→BS (ρ i) x y) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (M ∘ ρ) U w D BT T)
      (domainEvaluationProblem basis M U w D BS T) := by
  let prepare : MixedCode→Bits×List MixedCode := fun g => ([],[g.relabelBinary (finTable ρ)])
  let recover : Bits×List K→K := fun p => p.2.sum
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hq := ((fp_relabelBinary (finTable ρ)).pair (fp_const encoding encoding.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hq
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  have hqueries : ∀g,EncodedGraph BT T g→∀query∈(prepare g).2,EncodedGraph BS T query := by
    intro g hg query hq
    have he : query=g.relabelBinary (finTable ρ) := List.mem_singleton.mp hq
    subst query
    exact hg.relabelBinaryAlias ρ hB
  have hcorrect : ∀g (hg : EncodedGraph BT T g),
      recover ((prepare g).1,(prepare g).2.map (totalEvaluation M (extendedUnaries U D) w))=
        g.evaluate (hg.planarValid BT T).1 (M ∘ ρ) (extendedUnaries U D) w := by
    intro g hg
    have hv := (hg.planarValid BT T).1
    have hv' := relabelBinary_valid (finTable ρ) hv (lookup_finTable_lt ρ)
    change [totalEvaluation M (extendedUnaries U D) w (g.relabelBinary (finTable ρ))].sum=
      g.evaluate hv (M ∘ ρ) (extendedUnaries U D) w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M (extendedUnaries U D) w _ hv'] using
      evaluate_relabelBinary g hv ρ M (extendedUnaries U D) w
  let r := reductionOfPipeline basis BitEncoding.bits (M ∘ ρ) (extendedUnaries U D) w M (extendedUnaries U D) w
    (EncodedGraph BT T) (EncodedGraph BS T) (fun _ h => (h.planarValid BT T).1)
    (fun _ h => (h.planarValid BS T).1) prepare recover hp hr hqueries hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph BT T raw).mp h)
    (fun raw h => (encodedInput_iff_graph BS T raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Actual unary aliases include the reserved-offset lift, so existing domain
indicators move to the new offset without changing their prescribed sets. -/
noncomputable def domainUnaryRelabelReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→Fin b) (M : Fin bt→Matrix C C K) (U : Fin b→C→K) (w : C→K) (D : Fin d→Set C)
    (B : Fin bt→Fin d→Fin d→Prop) (TT : Fin a→Fin d→Prop) (TS : Fin b→Fin d→Prop)
    (hT : ∀i x,TT i x→TS (ρ i) x) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M (U ∘ ρ) w D B TT)
      (domainEvaluationProblem basis M U w D B TS) := by
  let lifted := liftUnaryAlias ρ d
  let prepare : MixedCode→Bits×List MixedCode := fun g => ([],[g.relabelUnary (finTable lifted)])
  let recover : Bits×List K→K := fun p => p.2.sum
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hq := ((fp_relabelUnary (finTable lifted)).pair (fp_const encoding encoding.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hq
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  have hqueries : ∀g,EncodedGraph B TT g→∀query∈(prepare g).2,EncodedGraph B TS query := by
    intro g hg query hq
    have he : query=g.relabelUnary (finTable lifted) := List.mem_singleton.mp hq
    subst query
    exact hg.relabelUnaryAlias ρ hT
  have hcorrect : ∀g (hg : EncodedGraph B TT g),
      recover ((prepare g).1,(prepare g).2.map (totalEvaluation M (extendedUnaries U D) w))=
        g.evaluate (hg.planarValid B TT).1 M (extendedUnaries (U ∘ ρ) D) w := by
    intro g hg
    have hv := (hg.planarValid B TT).1
    have hv' := relabelUnary_valid (finTable lifted) hv (lookup_finTable_lt lifted)
    change [totalEvaluation M (extendedUnaries U D) w (g.relabelUnary (finTable lifted))].sum=
      g.evaluate hv M (extendedUnaries (U ∘ ρ) D) w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M (extendedUnaries U D) w _ hv',
      lifted,extendedUnaries_comp_alias] using evaluate_relabelUnary g hv lifted M (extendedUnaries U D) w
  let r := reductionOfPipeline basis BitEncoding.bits M (extendedUnaries (U ∘ ρ) D) w M (extendedUnaries U D) w
    (EncodedGraph B TT) (EncodedGraph B TS) (fun _ h => (h.planarValid B TT).1)
    (fun _ h => (h.planarValid B TS).1) prepare recover hp hr hqueries hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph B TT raw).mp h)
    (fun raw h => (encodedInput_iff_graph B TS raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Appending a duplicate of an old binary constraint does not remove any
existing companion label and reduces by the explicit auxiliary-label alias. -/
noncomputable def domainBinaryDuplicateReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin ut→C→K) (w : C→K) (D : Fin d→Set C)
    (B : Fin b→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop) (old : Fin b) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (appendOne M (M old)) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U w D B T) := by
  have r := domainBinaryRelabelReduction basis (aliasAux old) M U w D (B ∘ aliasAux old) B T (fun _ _ _ h => h)
  simpa only [comp_aliasAux] using r

/-- Unary duplicate elimination also moves the reserved domain offsets while
retaining their original indices and all binary companions. -/
noncomputable def domainUnaryDuplicateReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix C C K) (U : Fin b→C→K) (w : C→K) (D : Fin d→Set C)
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin b→Fin d→Prop) (old : Fin b) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M (appendOne U (U old)) w D B (appendOne T (T old)))
      (domainEvaluationProblem basis M U w D B T) := by
  have r := domainUnaryRelabelReduction basis (aliasAux old) M U w D B (T ∘ aliasAux old) T (fun _ _ h => h)
  simpa only [comp_aliasAux] using r

end
end PlanarHom.Complexity.MixedCode
