import PlanarHom.FisherComponentCounts
import PlanarHom.FisherInheritedRowSemantics

/-! NEW exact preservation of ordinary graph components by the literal
numeric Fisher compiler, with original isolates retained as components. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCodePipeline
open Complexity MultiGraph Fisher FisherInheritedRowCode
variable {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)

 theorem intermediate_componentCount :
    ((intermediate g).toMultiGraph (intermediate_valid hg)).componentCount Finset.univ=
      (g.toMultiGraph hg).componentCount Finset.univ :=
  (FisherExpansionCode.computedIncidenceEquiv g hg).dartRelabel.componentCount.trans
    (Fisher.expansion_componentCount (FisherContourOrder.ordering g hg))

 theorem componentCount :
    ((code g).toMultiGraph (valid hg)).componentCount Finset.univ=
      (g.toMultiGraph hg).componentCount Finset.univ := by
  let R:=typedExpansionRows g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg)
  let p:=FisherCubicCode.ports (intermediate g) (intermediate_valid hg) (intermediate_cubic hg)
  have h₁:=(FisherCubicCode.incidenceEquiv (intermediate g) (intermediate_valid hg) (intermediate_cubic hg)).dartRelabel.componentCount
  have h₂:=Fisher.cubic_componentCount p R
  exact h₁.trans (h₂.trans (intermediate_componentCount hg))

 theorem incident : ∀v,∃a:MultiGraph.Kasteleyn.Dart (Fin (code g).edges.length),
    (((code g).toMultiGraph (valid hg)).dartPair a).1=v := by
  intro v
  let p:=FisherCubicCode.ports (intermediate g) (intermediate_valid hg) (intermediate_cubic hg)
  let i:=FisherCubicCode.incidenceEquiv (intermediate g) (intermediate_valid hg) (intermediate_cubic hg)
  obtain ⟨q,rfl⟩:=i.vertex.surjective v
  have hex:∃a:MultiGraph.Kasteleyn.Dart (Fin (intermediate g).edges.length⊕(Fin (intermediate g).vertices×Fin 3)),
      ((cubicDecoration p).dartPair a).1=q := by
    rcases q with ⟨v,j⟩
    fin_cases j
    · exact ⟨(Sum.inr (v,2),true),rfl⟩
    · exact ⟨(Sum.inr (v,0),true),rfl⟩
    · exact ⟨(Sum.inr (v,1),true),rfl⟩
  obtain ⟨a,ha⟩:=hex
  exact ⟨i.dartRelabel.dart a,(i.dartRelabel.host a).trans (congrArg i.vertex ha)⟩

end PlanarHom.FisherCodePipeline
