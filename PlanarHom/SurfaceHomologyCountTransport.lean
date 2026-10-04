import PlanarHom.SurfaceGlobalHomologyBound
import PlanarHom.FisherGlobalEuler
import PlanarHom.FisherNumericRotationTransport

/-! NEW global homology dimension expressed using literal cycle counts and
transported under actual occurrence/dart relabeling. -/
noncomputable section
open Classical
open Matrix Module
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn SurfaceRibbonComplement FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] [targetDec:DecidableEq (Dart E)]
variable {G:MultiGraph V E} (R:RotationRows G)

 theorem homology_finrank_count_euler :
    finrank (ZMod 2) R.Homology+Fintype.card V+count R.facePerm+Fintype.card (Isolated (G:=G))=
      Fintype.card E+2*G.componentCount Finset.univ := by
  have h:=R.homology_finrank_ribbon_euler
  have hc:Fintype.card R.Face=count R.facePerm:=Nat.card_eq_fintype_card.symm
  rw [Fintype.card_sum,hc] at h
  omega

 theorem isolate_card_zero_of_incident (hinc:∀v,∃a:Dart E,(G.dartPair a).1=v) :
    Fintype.card (Isolated (G:=G))=0 := by
  letI : IsEmpty (Isolated (G:=G)):=⟨fun v=>by obtain ⟨a,ha⟩:=hinc v.val; exact v.property a ha⟩
  exact Fintype.card_eq_zero

 theorem homology_finrank_incident (hinc:∀v,∃a:Dart E,(G.dartPair a).1=v) :
    finrank (ZMod 2) R.Homology+Fintype.card V+count R.facePerm=
      Fintype.card E+2*G.componentCount Finset.univ := by
  have h:=R.homology_finrank_count_euler
  rw [isolate_card_zero_of_incident hinc,add_zero] at h
  exact h

 theorem redecidable_homology_finrank {sourceDec:DecidableEq (Dart E)}
    (S:@RotationRows V E G sourceDec) :
    (letI : DecidableEq (Dart E) := targetDec;
      finrank (ZMod 2) (@redecidable V E G sourceDec targetDec S).Homology)=finrank (ZMod 2) S.Homology := by
  have h:sourceDec=targetDec:=Subsingleton.elim _ _
  subst targetDec
  rfl

end PlanarHom.PlanarityLRRealization.RotationRows
namespace PlanarHom.MultiGraph.DartRelabel
open Kasteleyn PlanarityLRRealization SurfaceRibbonComplement
variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]
variable {G:MultiGraph V E} {H:MultiGraph W F} (e:DartRelabel G H)

 def isolatedEquiv : Isolated (G:=G)≃Isolated (G:=H) where
  toFun v:=⟨e.vertex v.val,by
    intro b hb
    obtain ⟨a,rfl⟩:=e.dart.surjective b
    exact v.property a (e.vertex.injective ((e.host a).symm.trans hb))⟩
  invFun w:=⟨e.vertex.symm w.val,by
    intro a ha
    apply w.property (e.dart a)
    rw [e.host,ha,Equiv.apply_symm_apply]⟩
  left_inv v:=Subtype.ext (e.vertex.symm_apply_apply v.val)
  right_inv w:=Subtype.ext (e.vertex.apply_symm_apply w.val)

 theorem homology_finrank (R:RotationRows G) :
    finrank (ZMod 2) (e.rows R).Homology=finrank (ZMod 2) R.Homology := by
  have hs:=R.homology_finrank_count_euler
  have ht:=(e.rows R).homology_finrank_count_euler
  rw [e.face_count,e.componentCount] at ht
  have hv:=Fintype.card_congr e.vertex
  have hi:=Fintype.card_congr e.isolatedEquiv
  have he:=e.edge_card
  omega

end PlanarHom.MultiGraph.DartRelabel
