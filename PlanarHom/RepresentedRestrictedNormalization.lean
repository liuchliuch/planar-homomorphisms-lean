import PlanarHom.RepresentedProductContracts

/-! Proof restrictions do not add a runtime promise test. The normalizer acts
on the same successful raw word and returns the same canonical underlying code. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.BitEncoding
open MachineComposition

@[simp] theorem restrict_decode_some_iff {α:Type} (e:BitEncoding α) (P:α→Prop)
    (w:Bits) (a:{a//P a}) :
    (e.restrict P).decode w=some a ↔ e.decode w=some a.val := by
  unfold restrict
  simp only
  cases hd:e.decode w with
  | none=>simp [hd]
  | some b=>
    by_cases hb:P b
    · simp [hd,hb,Subtype.ext_iff]
    · have hn:b≠a.val:=fun h=>hb (h ▸ a.property)
      simp [hd,hb,hn]

def restrictedWord {α:Type} (e:BitEncoding α) (P:α→Prop)
    (w:ValidWord (e.restrict P)) : ValidWord e :=
  ⟨w.raw,by
    obtain ⟨a,ha⟩:=w.property
    exact ⟨a.val,(restrict_decode_some_iff e P _ a).mp ha⟩⟩

theorem restrictedWord_value {α:Type} (e:BitEncoding α) (P:α→Prop)
    (w:ValidWord (e.restrict P)) :
    (restrictedWord e P w).value=w.value.val := by
  apply ValidWord.value_eq
  exact (restrict_decode_some_iff e P _ w.value).mp w.decode_raw

/-- Actual lexical normalization on a proof-restricted type, without a machine
for deciding the restriction. Its input promise is retained explicitly. -/
def restrictNormalizer {α:Type} (e:BitEncoding α) (P:α→Prop) (h:Normalizer e) :
    Normalizer (e.restrict P) := by
  let c:=transportInputComputer (ValidWord.encoding (e.restrict P))
    (ValidWord.encoding e) e (restrictedWord e P) (fun _=>rfl) h
  apply transportOutputComputer (ValidWord.encoding (e.restrict P)) e (e.restrict P)
    (computer:=c)
  intro w
  simp only [Function.comp_apply,restrictedWord_value]
  rfl

end PlanarHom.Complexity.BitEncoding
namespace PlanarHom.RepresentedBit
open Complexity
variable {K:Type} [CommSemiring K]

def Presentation.validated (P:Presentation K) : Presentation K where
  Code:=ValidCode P
  encoding:=validEncoding P
  valid:=fun _=>True
  value:=validValue P
  complete:=by intro x; obtain ⟨a,ha,hx⟩:=P.complete x; exact ⟨⟨a,ha⟩,trivial,hx⟩
  normalizer:=BitEncoding.restrictNormalizer P.encoding P.valid P.normalizer

theorem Presentation.validated_represents (P:Presentation K) (raw:Bits) (x:K) :
    P.validated.Represents raw x ↔ P.Represents raw x := by
  constructor
  · rintro ⟨a,ha,_,hx⟩
    exact ⟨a.val,(BitEncoding.restrict_decode_some_iff P.encoding P.valid raw a).mp ha,a.property,hx⟩
  · rintro ⟨a,ha,hv,hx⟩
    exact ⟨⟨a,hv⟩,(BitEncoding.restrict_decode_some_iff P.encoding P.valid raw ⟨a,hv⟩).mpr ha,trivial,hx⟩

theorem Presentation.validated_problem (P:Presentation K) {A:Type} (ea:BitEncoding A)
    (H:A→Prop) (f:A→K) : P.validated.problem ea H f=P.problem ea H f := by
  unfold Presentation.problem typedProblem
  congr 1
  funext raw out
  apply propext
  exact forall_congr' (fun a=>imp_congr_right (fun _=>imp_congr_right
      (fun _=>P.validated_represents out (f a))))

end PlanarHom.RepresentedBit
