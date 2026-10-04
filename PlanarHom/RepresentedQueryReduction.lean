import PlanarHom.RepresentedPresentationPipeline
import PlanarHom.RepresentedFixedLinearArithmetic
import PlanarHom.ListMutationMachines

noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity PairProjectionMachines
variable {K D Q:Type} [CommSemiring K]

/-- One actual structural query with unchanged semantic answer. The answer is
lexically normalized, rather than assumed to be a preferred representative. -/
def queryReduction (P:Presentation K) (ed:BitEncoding D) (eq:BitEncoding Q)
    (nd:BitEncoding.Normalizer ed) (H:D→Prop) (HQ:Q→Prop) (target:D→K) (source:Q→K)
    (query:D→Q) (hq:FP ed eq query) (legal:∀a,H a→HQ (query a))
    (correct:∀a,H a→source (query a)=target a) :
    Reduction (P.problem ed H target) (P.problem eq HQ source) := by
  let prepare:D→ℕ×List Q:=fun a=>(0,[query a])
  let recover:ℕ×List P.Code→P.Code:=fun p=>p.2.headD (P.constant 0)
  have hp:FP ed (BitEncoding.nat.prod eq.list) prepare:=
    (fp_const ed BitEncoding.nat 0).pair ((hq.pair (fp_const ed eq.list [])).comp (ListMutationMachines.fp_cons eq))
  have hr:FP (BitEncoding.nat.prod P.encoding.list) P.encoding recover:=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD P.encoding (P.constant 0))
  apply presentationPipeline P P ed BitEncoding.nat eq nd BitEncoding.natNormalizer H HQ target source
    prepare recover hp hr
  · intro a ha q hmem
    have he:q=query a:=List.mem_singleton.mp hmem
    exact he ▸ legal a ha
  · intro a ha bs hbs
    change List.Forall₂ _ [query a] bs at hbs
    cases hbs with
    | cons hrel hrest=>
      cases hrest
      exact ⟨hrel.1,hrel.2.trans (correct a ha)⟩

end PlanarHom.RepresentedBit
