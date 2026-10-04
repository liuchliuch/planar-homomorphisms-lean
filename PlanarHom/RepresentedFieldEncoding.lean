import PlanarHom.RepresentedBitFPClosure
import PlanarHom.RationalCoordinateNormalizers

/-! A concrete, possibly nonunique presentation has a code type, validity,
semantic value and an actual lexical normalizer. It never demands injective
encoding of mathematical field values. Output relations name the prescribed
presentation explicitly, so changing an auxiliary field requires proved descent. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity ArithmeticCircuitPrimitives

structure Presentation (K:Type) where
  Code : Type
  encoding : BitEncoding Code
  valid : Code→Prop
  value : Code→K
  complete : ∀x:K,∃c,valid c ∧ value c=x
  normalizer : BitEncoding.Normalizer encoding

def Presentation.Represents {K:Type} (P:Presentation K) (raw:Bits) (x:K) : Prop :=
  ∃c,P.encoding.decode raw=some c ∧ P.valid c ∧ P.value c=x

def Presentation.product {K L:Type} (P:Presentation K) (Q:Presentation L) : Presentation (K×L) where
  Code:=P.Code×Q.Code
  encoding:=P.encoding.prod Q.encoding
  valid:=fun c=>P.valid c.1 ∧ Q.valid c.2
  value:=fun c=>(P.value c.1,Q.value c.2)
  complete:=by
    rintro ⟨x,y⟩
    obtain ⟨a,ha,hx⟩:=P.complete x
    obtain ⟨b,hb,hy⟩:=Q.complete y
    exact ⟨(a,b),⟨ha,hb⟩,Prod.ext hx hy⟩
  normalizer:=BitEncoding.prodNormalizer P.normalizer Q.normalizer

/-- All successfully decoded raw inputs satisfying H are admitted, and every
output code satisfying R is accepted. No canonical field answer is selected. -/
def typedProblem {A B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (H:A→Prop) (R:A→B→Prop) : Problem where
  valid:=fun raw=>∃a,ea.decode raw=some a ∧ H a
  answer:=fun raw out=>∀a,ea.decode raw=some a→H a→∃b,eb.decode out=some b ∧ R a b

private def inputView {A B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (H:A→Prop) (R:A→B→Prop) (x:{raw:Bits // (typedProblem ea eb H R).valid raw}) :
    BitEncoding.ValidWord ea := ⟨x.val,by obtain ⟨a,hd,ha⟩:=x.property; exact ⟨a,hd⟩⟩

/-- A concrete bit-costed code transformer realizes its semantic relation on
arbitrary raw lexical encodings. The normalizer is an actual required machine. -/
theorem typedProblem_inFP {A B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (normalizer:BitEncoding.Normalizer ea) (H:A→Prop) (R:A→B→Prop)
    (f:A→B) (hf:FP ea eb f) (hcorrect:∀a,H a→R a (f a)) :
    (typedProblem ea eb H R).InFP := by
  let view:=inputView ea eb H R
  have hv:FP (BitEncoding.bits.restrict (typedProblem ea eb H R).valid)
      (BitEncoding.ValidWord.encoding ea) view:=fp_code_view _ _ _ (fun _=>rfl)
  have hn:=hv.comp ⟨normalizer⟩
  have hcalc:=hn.comp hf
  have hraw:=hcalc.comp (fp_code_view eb BitEncoding.bits eb.encode (fun _=>rfl))
  refine ⟨fun x=>eb.encode (f (view x).value),hraw,?_⟩
  intro x a hd ha
  have he:(view x).value=a:=BitEncoding.ValidWord.value_eq hd
  refine ⟨f a,?_,hcorrect a ha⟩
  change eb.decode (eb.encode (f (view x).value))=some (f a)
  rw [he,eb.decode_encode]

/-- The semantic output field is the codomain of this fixed presentation. -/
def Presentation.problem {K A:Type} (P:Presentation K) (ea:BitEncoding A)
    (H:A→Prop) (f:A→K) : Problem :=
  typedProblem ea P.encoding H (fun a b=>P.valid b ∧ P.value b=f a)

theorem Presentation.problem_inFP {K A:Type} (P:Presentation K) (ea:BitEncoding A)
    (normalizer:BitEncoding.Normalizer ea) (H:A→Prop) (f:A→K) (run:A→P.Code)
    (hrun:FP ea P.encoding run)
    (hvalid:∀a,H a→P.valid (run a)) (hvalue:∀a,H a→P.value (run a)=f a) :
    (P.problem ea H f).InFP :=
  typedProblem_inFP ea P.encoding normalizer H _ run hrun (fun a ha=>⟨hvalid a ha,hvalue a ha⟩)

end PlanarHom.RepresentedBit
