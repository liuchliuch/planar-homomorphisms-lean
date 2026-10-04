import PlanarHom.PrescribedDomainAliasReductions
import PlanarHom.OracleReductionLaws

/-! NEW RECONSTRUCTION (2026-10-02), not a recovered original body.
Exact transport for the baseline raw prescribed-domain codec. Ordinary labels,
ordered edges, unaries, multiplicities and the coefficient field are retained.
Only intrinsic reserved-domain labels are renamed by a fixed finite table.
Color transport is an equality of the complete raw field-coded value function.
-/
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLabelLookupMachines
variable {a b bt ut : ℕ}

/-- Keep every ordinary unary label and rename only the reserved domain suffix. -/
def liftDomainAlias (ρ : Fin a → Fin b) (ut : ℕ) : Fin (ut+a) → Fin (ut+b) :=
  Fin.addCases (Fin.castAdd b) (fun d => Fin.natAdd ut (ρ d))

@[simp] theorem liftDomainAlias_regular (ρ : Fin a → Fin b) (i : Fin ut) :
    liftDomainAlias ρ ut (Fin.castAdd a i) = Fin.castAdd b i := Fin.addCases_left _

@[simp] theorem liftDomainAlias_reserved (ρ : Fin a → Fin b) (i : Fin a) :
    liftDomainAlias ρ ut (Fin.natAdd ut i) = Fin.natAdd ut (ρ i) := Fin.addCases_right _

theorem lookup_domainAlias_regular (ρ : Fin a → Fin b) (i : Fin ut) :
    lookup (finTable (liftDomainAlias ρ ut)) i.val = i.val := by
  change lookup (finTable (liftDomainAlias ρ ut)) (Fin.castAdd a i).val = _
  rw [lookup_finTable, liftDomainAlias_regular]
  rfl

theorem lookup_domainAlias_reserved (ρ : Fin a → Fin b) (i : Fin a) :
    lookup (finTable (liftDomainAlias ρ ut)) (ut+i.val) = ut+(ρ i).val := by
  change lookup (finTable (liftDomainAlias ρ ut)) (Fin.natAdd ut i).val = _
  rw [lookup_finTable, liftDomainAlias_reserved]
  rfl

/-- Literal graph-code identity, including the original unary occurrence list. -/
theorem relabelDomains_withDomains (ρ : Fin a → Fin b)
    (g : MixedCode) (hg : g.Valid bt ut) (δ : Fin g.vertices → Fin a) :
    (withDomains (unaryTypes:=ut) g δ).relabelUnary (finTable (liftDomainAlias ρ ut)) =
      withDomains (unaryTypes:=ut) g (ρ ∘ δ) := by
  simp only [relabelUnary, withDomains, domainOccurrences, List.map_append, List.map_ofFn]
  congr 1
  apply congrArg₂ List.append
  · conv_rhs => rw [← List.map_id g.unaries]
    apply List.map_congr_left
    intro u hu
    rw [lookup_domainAlias_regular ρ ⟨u.2, (hg.2 u hu).2⟩]
    rfl
  · apply congrArg List.ofFn
    funext v
    dsimp only [Function.comp_apply]
    rw [lookup_domainAlias_reserved]

/-- The original typed graph is unchanged; its vertex-domain assignment follows ρ. -/
theorem Typed.reindexDomains (ρ : Fin a → Fin b)
    {BT : Fin bt → Fin a → Fin a → Prop} {BS : Fin bt → Fin b → Fin b → Prop}
    {TT : Fin ut → Fin a → Prop} {TS : Fin ut → Fin b → Prop}
    (hB : ∀ l x y, BT l x y → BS l (ρ x) (ρ y))
    (hT : ∀ l x, TT l x → TS l (ρ x))
    {g : MixedCode} {hg : g.Valid bt ut} {δ : Fin g.vertices → Fin a}
    (h : Typed BT TT g hg δ) : Typed BS TS g hg (ρ ∘ δ) :=
  ⟨fun e he => hB _ _ _ (h.1 e he), fun u hu => hT _ _ (h.2 u hu)⟩

theorem EncodedGraph.reindexDomains (ρ : Fin a → Fin b)
    {BT : Fin bt → Fin a → Fin a → Prop} {BS : Fin bt → Fin b → Fin b → Prop}
    {TT : Fin ut → Fin a → Prop} {TS : Fin ut → Fin b → Prop}
    (hB : ∀ l x y, BT l x y → BS l (ρ x) (ρ y))
    (hT : ∀ l x, TT l x → TS l (ρ x))
    {g : MixedCode} (h : EncodedGraph BT TT g) :
    EncodedGraph BS TS (g.relabelUnary (finTable (liftDomainAlias ρ ut))) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=ut) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [relabelDomains_withDomains ρ original hg δ]
  exact encodedInput_encode_withDomains (ht.reindexDomains ρ hB hT) hp

section Values
variable {C R : Type} [CommSemiring R]

theorem extendedUnaries_comp_domainAlias (ρ : Fin a → Fin b)
    (U : Fin ut → C → R) (D : Fin b → Set C) :
    extendedUnaries U D ∘ liftDomainAlias ρ ut = extendedUnaries U (D ∘ ρ) := by
  funext i c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [Function.comp_apply, liftDomainAlias, extendedUnaries]

end Values
end PlanarHom.PrescribedDomains

namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.PrescribedDomains PlanarHom.FiniteLabelLookupMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension a b bt ut : ℕ}

/-- A genuinely compiled one-query reduction. No new domains, free pins, field
identifications, or supplied polynomial-time transducers are assumed. -/
def domainReindexReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a → Fin b) (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (w : C → K) (D : Fin b → Set C)
    (BT : Fin bt → Fin a → Fin a → Prop) (BS : Fin bt → Fin b → Fin b → Prop)
    (TT : Fin ut → Fin a → Prop) (TS : Fin ut → Fin b → Prop)
    (hB : ∀ l x y, BT l x y → BS l (ρ x) (ρ y))
    (hT : ∀ l x, TT l x → TS l (ρ x)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w (D ∘ ρ) BT TT)
      (domainEvaluationProblem basis M U w D BS TS) := by
  let lifted := liftDomainAlias ρ ut
  let prepare : MixedCode → Bits × List MixedCode :=
    fun g => ([], [g.relabelUnary (finTable lifted)])
  let recover : Bits × List K → K := fun p => p.2.sum
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hq := ((fp_relabelUnary (finTable lifted)).pair (fp_const encoding encoding.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hq
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  have hqueries : ∀ g, EncodedGraph BT TT g → ∀ query ∈ (prepare g).2, EncodedGraph BS TS query := by
    intro g hg query hq
    have he : query = g.relabelUnary (finTable lifted) := List.mem_singleton.mp hq
    subst query
    exact hg.reindexDomains ρ hB hT
  have hcorrect : ∀ g (hg : EncodedGraph BT TT g),
      recover ((prepare g).1, (prepare g).2.map (totalEvaluation M (extendedUnaries U D) w)) =
        g.evaluate (hg.planarValid BT TT).1 M (extendedUnaries U (D ∘ ρ)) w := by
    intro g hg
    have hv := (hg.planarValid BT TT).1
    have hv' := relabelUnary_valid (finTable lifted) hv (lookup_finTable_lt lifted)
    change [totalEvaluation M (extendedUnaries U D) w (g.relabelUnary (finTable lifted))].sum = _
    simpa only [List.sum_cons, List.sum_nil, add_zero,
      totalEvaluation_valid M (extendedUnaries U D) w _ hv', lifted,
      extendedUnaries_comp_domainAlias] using
      evaluate_relabelUnary g hv lifted M (extendedUnaries U D) w
  let r := reductionOfPipeline basis BitEncoding.bits M (extendedUnaries U (D ∘ ρ)) w
    M (extendedUnaries U D) w (EncodedGraph BT TT) (EncodedGraph BS TS)
    (fun _ h => (h.planarValid BT TT).1) (fun _ h => (h.planarValid BS TS).1)
    prepare recover hp hr hqueries hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph BT TT raw).mp h)
    (fun raw h => (encodedInput_iff_graph BS TS raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

end
end PlanarHom.Complexity.MixedCode
