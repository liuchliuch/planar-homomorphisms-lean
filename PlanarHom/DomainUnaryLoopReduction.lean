import PlanarHom.DomainUnaryLoopTransform
import PlanarHom.PromiseReductionTransport

/-! Actual raw-bit diagonal-unary realization with exact domain metadata and
unchanged positive or signed background weights. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.MixedCode
open PlanarHom PrescribedDomains PairProjectionMachines FiniteLanguageAliases FiniteLabelLookupMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {b u d dimension : ℕ}

def domainDiagonalUnaryAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (D : Fin d→Set C) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (selected : Fin b) (TV : Fin d→Prop) (hloop : ∀x,TV x→B selected x x) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis M (appendOne U (fun i=>M selected i i)) w D B (appendOne T TV))
      (domainEvaluationProblem basis M U w D B T) := by
  let HT := EncodedGraph B (appendOne T TV)
  let HS := EncodedGraph B T
  let transform := domainUnaryLoopTransform u d selected.val
  have vt : ∀g,HT g→g.Valid b (u+1+d) := fun _ h=>(h.planarValid _ _).1
  have vs : ∀g,HS g→g.Valid b (u+d) := fun _ h=>(h.planarValid _ _).1
  have hq : ∀g,HT g→HS (transform g) := fun _ h=>h.domainUnaryLoopTransform selected hloop
  have hc : ∀g (hg : HT g),totalEvaluation M (extendedUnaries U D) w (transform g)=
      g.evaluate (vt g hg) M (extendedUnaries (appendOne U (fun i=>M selected i i)) D) w := by
    intro g hg
    rw [totalEvaluation_valid _ _ _ _ (vs _ (hq g hg))]
    have hv := relabelUnary_valid (finTable (auxUnaryLast u d)) (vt g hg) (lookup_finTable_lt _)
    have h := (evaluate_realizeUnaryLoops selected (g.relabelUnary (finTable (auxUnaryLast u d))) hv
      M (extendedUnaries U D) w).trans
      (evaluate_relabelUnary g (vt g hg) (auxUnaryLast u d) M
        (appendOne (extendedUnaries U D) (fun i=>M selected i i)) w)
    rw [extendedUnaries_auxUnaryLast] at h
    exact h
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) (fun g=>([],[transform g])) := by
    have hl := ((fp_domainUnaryLoopTransform u d selected.val).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  let r := reductionOfPipeline basis BitEncoding.bits M
    (extendedUnaries (appendOne U (fun i=>M selected i i)) D) w M (extendedUnaries U D) w
    HT HS vt vs (fun g=>([],[transform g])) (fun p : Bits×List K=>p.2.sum) hp
    ((fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis))
    (by intro g hg query h; obtain rfl := List.mem_singleton.mp h; exact hq g hg)
    (by intro g hg; simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hc g hg)
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph B (appendOne T TV) raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.Complexity.MixedCode
