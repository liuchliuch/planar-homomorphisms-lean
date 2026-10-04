import PlanarHom.TypedGadgetAppendCompiler
import PlanarHom.HeterogeneousGraphReduction
import PlanarHom.PromiseReductionTransport

/-! Full raw-word, bit-costed domain-preserving template substitution.
Only the fixed original source basis and exact source-domain oracle are used. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open Complexity Complexity.MixedCode PrescribedDomains FixedGadgetNetwork EdgeSubstitution
open PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension bt ut dt : ℕ}

/-- One actual finite query. Arbitrary old unary companions and intrinsic
metadata are unchanged, and all private assignments are summed literally. -/
def familyReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ts : List Template) (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (BT : Fin ts.length → Fin dt → Fin dt → Prop)
    (fallback : Fin dt)
    (ht : ∀t∈ts,t.code.Valid bt (ut+dt)) (hb : ∀t∈ts,t.boundary=2)
    (hp : ∀t (h:t∈ts),TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hb t h) (ht t h)))
    (hfamily : FamilyTyping (ut:=ut) ts B BT) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (interactions ts M (extendedUnaries U D)) U (fun _=>1) D BT T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let HT := EncodedGraph BT T
  let HS := EncodedGraph B T
  have validT : ∀g,HT g → g.Valid ts.length (ut+dt) := fun _ h=>(h.planarValid BT T).1
  have validS : ∀g,HS g → g.Valid bt (ut+dt) := fun _ h=>(h.planarValid B T).1
  let prepare : MixedCode → Bits × List MixedCode := fun g=>([],[substitute ts g])
  let recover : Bits × List K → K := fun z=>z.2.sum
  have hprepare : FP MixedCode.encoding (BitEncoding.bits.prod MixedCode.encoding.list) prepare :=
    (fp_const MixedCode.encoding BitEncoding.bits []).pair
      (((fp_substitute ts).pair (fp_const MixedCode.encoding MixedCode.encoding.list [])).comp
        (ListMutationMachines.fp_cons MixedCode.encoding))
  have hrecover : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) recover :=
    (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (MaterializedFieldListMachines.fp_sum basis)
  let r := reductionOfHeterogeneousPipeline basis BitEncoding.bits
    (interactions ts M (extendedUnaries U D)) (extendedUnaries U D) (fun _=>1)
    M (extendedUnaries U D) (fun _=>1) HT HS validT validS prepare recover hprepare hrecover
    (by
      intro g hg q hq
      obtain rfl := List.mem_singleton.mp hq
      exact substitute_encodedGraph ts B T BT fallback ht hb hp hfamily hg)
    (by
      intro g hg
      simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid M (extendedUnaries U D) (fun _=>1) _
        (substitute_valid ts ht hb g (validT g hg))]
      exact evaluate_substitute ts ht hb g (validT g hg) M (extendedUnaries U D))
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph BT T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h)
    (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.TypedGadgetAppend
