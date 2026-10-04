import PlanarHom.RepresentedNonadaptiveCompiler
import PlanarHom.RepresentedAnswerLists

/-! A typed preparation/recovery pipeline over honest nonunique presentations
lifts to an actual represented-output oracle reduction. Postprocessing accepts
all decodable valid answer representatives through actual lexical normalizers. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity MachineComposition

private def inputView {A K:Type} (P:Presentation K) (ea:BitEncoding A)
    (H:A→Prop) (f:A→K) (raw:Bits) (h:(P.problem ea H f).valid raw) : BitEncoding.ValidWord ea :=
  ⟨raw,by obtain ⟨a,hd,ha⟩:=h; exact ⟨a,hd⟩⟩

private theorem inputView_property {A K:Type} (P:Presentation K) (ea:BitEncoding A)
    (H:A→Prop) (f:A→K) (raw:Bits) (h:(P.problem ea H f).valid raw) :
    H (inputView P ea H f raw h).value := by
  obtain ⟨a,hd,ha⟩:=h
  have he:(inputView P ea H f raw ⟨a,hd,ha⟩).value=a:=BitEncoding.ValidWord.value_eq hd
  rwa [he]

def presentationPipeline {A C Q K L:Type}
    (PS:Presentation K) (PT:Presentation L)
    (ea:BitEncoding A) (ec:BitEncoding C) (eq:BitEncoding Q)
    (na:BitEncoding.Normalizer ea) (nc:BitEncoding.Normalizer ec)
    (HT:A→Prop) (HS:Q→Prop) (targetValue:A→L) (sourceValue:Q→K)
    (prepare:A→C×List Q) (recover:C×List PS.Code→PT.Code)
    (hp:FP ea (ec.prod eq.list) prepare)
    (hr:FP (ec.prod PS.encoding.list) PT.encoding recover)
    (queriesValid:∀a,HT a→∀q∈(prepare a).2,HS q)
    (correct:∀a,HT a→∀bs,List.Forall₂ (fun q b=>PS.valid b ∧ PS.value b=sourceValue q) (prepare a).2 bs→
      PT.valid (recover ((prepare a).1,bs)) ∧ PT.value (recover ((prepare a).1,bs))=targetValue a) :
    Reduction (PT.problem ea HT targetValue) (PS.problem eq HS sourceValue) := by
  let target:=PT.problem ea HT targetValue
  let source:=PS.problem eq HS sourceValue
  let view:=inputView PT ea HT targetValue
  let postEncoding:=ec.prod PS.encoding.list
  let postNormalizer:=BitEncoding.prodNormalizer nc (BitEncoding.listNormalizer PS.normalizer)
  let pre:=composeComputers na (Classical.choice hp)
  let rawRecover:C×List PS.Code→Bits:=fun p=>PT.encoding.encode (recover p)
  have hrawRecover:FP postEncoding BitEncoding.bits rawRecover:=hr.comp
    (fp_code_view PT.encoding BitEncoding.bits PT.encoding.encode (fun _=>rfl))
  let post:=composeComputers postNormalizer (Classical.choice hrawRecover)
  let recoverWord:BitEncoding.ValidWord postEncoding→Bits:=fun r=>rawRecover r.value
  have hvalid:∀raw h,HT (view raw h).value:=inputView_property PT ea HT targetValue
  have pdata:∀raw h (answers:Q→Bits),
      (∀q∈(prepare (view raw h).value).2,source.answer (eq.encode q) (answers q))→
      ∃r:BitEncoding.ValidWord postEncoding,
        (BitEncoding.ValidWord.encoding postEncoding).encode r=
          (ec.prod BitEncoding.bits.list).encode ((prepare (view raw h).value).1,(prepare (view raw h).value).2.map answers) ∧
        target.answer raw (recoverWord r) := by
    intro raw h answers ha
    let a:=(view raw h).value
    have hcodes:∀q∈(prepare a).2,∃b,PS.encoding.decode (answers q)=some b ∧ PS.valid b ∧ PS.value b=sourceValue q := by
      intro q hq
      exact ha q hq q (eq.decode_encode q) (queriesValid a (hvalid raw h) q hq)
    obtain ⟨bs,hd,hbs⟩:=answer_list_codes PS.encoding (prepare a).2 answers
      (fun q b=>PS.valid b ∧ PS.value b=sourceValue q) hcodes
    let word:=(ec.prod BitEncoding.bits.list).encode ((prepare a).1,(prepare a).2.map answers)
    have hdecode:postEncoding.decode word=some ((prepare a).1,bs):=
      decode_context_answers ec PS.encoding (prepare a).1 _ bs hd
    let r:BitEncoding.ValidWord postEncoding:=⟨word,⟨((prepare a).1,bs),hdecode⟩⟩
    have hrvalue:r.value=((prepare a).1,bs):=BitEncoding.ValidWord.value_eq hdecode
    refine ⟨r,rfl,?_⟩
    change ∀a',ea.decode raw=some a'→HT a'→∃b,PT.encoding.decode (recoverWord r)=some b ∧
      PT.valid b ∧ PT.value b=targetValue a'
    intro a' hda' hta'
    have he:a=a':=BitEncoding.ValidWord.value_eq hda'
    have hc:=correct a (hvalid raw h) bs hbs
    refine ⟨recover ((prepare a).1,bs),?_,hc.1,?_⟩
    · change PT.encoding.decode (PT.encoding.encode (recover r.value))=some _
      rw [hrvalue,PT.encoding.decode_encode]
    · exact hc.2.trans (congrArg targetValue he)
  exact compileNonadaptive (BitEncoding.ValidWord.encoding ea) ec eq
    (BitEncoding.ValidWord.encoding postEncoding) target source
    (fun a=>prepare a.value) recoverWord pre post view (fun _ _=>rfl)
    (fun raw h q hq=>⟨q,eq.decode_encode q,queriesValid _ (hvalid raw h) q hq⟩)
    (fun raw h answers ha=>Classical.choose (pdata raw h answers ha))
    (fun raw h answers ha=>(Classical.choose_spec (pdata raw h answers ha)).1)
    (fun raw h answers ha=>(Classical.choose_spec (pdata raw h answers ha)).2)

end PlanarHom.RepresentedBit
