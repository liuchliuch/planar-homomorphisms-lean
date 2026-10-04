import PlanarHom.RepresentedQueryReduction
import PlanarHom.RepresentedReductionComposition

/-! Actual one-query change of answer presentation. The converter consumes any
valid representative the oracle returns, with no preferred-size oracle. Both
forward embeddings and membership-promised output descent use this same map. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity PairProjectionMachines
variable {K L D:Type} [CommSemiring K]

def answerConversionReduction (PS:Presentation K) (PT:Presentation L)
    (ed:BitEncoding D) (nd:BitEncoding.Normalizer ed) (H:D→Prop) (source:D→K) (target:D→L)
    (convert:PS.Code→PT.Code) (hc:FP PS.encoding PT.encoding convert)
    (correct:∀a,H a→∀c,PS.valid c→PS.value c=source a→PT.valid (convert c) ∧ PT.value (convert c)=target a) :
    Reduction (PT.problem ed H target) (PS.problem ed H source) := by
  let prep:D→ℕ×List D:=fun a=>(0,[a])
  let recov:ℕ×List PS.Code→PT.Code:=fun p=>convert (p.2.headD (PS.constant 0))
  have hp:FP ed (BitEncoding.nat.prod ed.list) prep:=
    (fp_const ed BitEncoding.nat 0).pair (((fp_id ed).pair (fp_const ed ed.list [])).comp (ListMutationMachines.fp_cons ed))
  have hr:FP (BitEncoding.nat.prod PS.encoding.list) PT.encoding recov:=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD PS.encoding (PS.constant 0))).comp hc
  apply presentationPipeline PS PT ed BitEncoding.nat ed nd BitEncoding.natNormalizer H H target source
    prep recov hp hr
  · intro a ha q hq
    have he:q=a:=List.mem_singleton.mp hq
    exact he ▸ ha
  · intro a ha bs hbs
    change List.Forall₂ _ [a] bs at hbs
    cases hbs with
    | cons hrel hrest=>
      cases hrest
      exact correct a ha _ hrel.1 hrel.2

end PlanarHom.RepresentedBit
