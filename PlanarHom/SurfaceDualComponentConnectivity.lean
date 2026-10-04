import PlanarHom.SurfaceRibbonComplement

/-! NEW typed dual-component connectivity over an arbitrary disconnected
rotation system. No connected-input premise is used. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn SurfaceRibbonComplement
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G:MultiGraph V E} (R:RotationRows G)

 theorem incident_of_component (a:Dart E) (v:V)
    (h:G.componentSetoid Finset.univ (G.dartPair a).1 v) : ∃b:Dart E,(G.dartPair b).1=v := by
  let p:=fun u:V=>∃b:Dart E,(G.dartPair b).1=u
  have hc:G.EdgeConstant Finset.univ p := by
    intro e he
    apply propext
    exact ⟨fun _=>⟨(e,false),rfl⟩,fun _=>⟨(e,true),rfl⟩⟩
  have he:=G.edgeConstant_respects Finset.univ p hc h
  exact Eq.mp he ⟨a,rfl⟩

 theorem dual_connected_of_primal (a b:Dart E)
    (h:G.componentSetoid Finset.univ (G.dartPair a).1 (G.dartPair b).1) :
    R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf b) := by
  have lift:∀u v,G.componentSetoid Finset.univ u v→∀a b:Dart E,
      (G.dartPair a).1=u→(G.dartPair b).1=v→
      R.dualGraph.componentSetoid Finset.univ (R.faceOf a) (R.faceOf b) := by
    intro u v huv
    induction huv with
    | rel u v h=>
      obtain ⟨e,he,rfl,rfl⟩:=h
      intro a b ha hb
      exact Relation.EqvGen.trans _ _ _ (R.dual_connected_sameHost a (e,true) ha)
        (Relation.EqvGen.trans _ _ _ (R.dual_connected_reverse (e,true))
          (R.dual_connected_sameHost (e,false) b hb.symm))
    | refl u=>
      intro a b ha hb
      exact R.dual_connected_sameHost a b (ha.trans hb.symm)
    | symm u v h ih=>
      intro a b ha hb
      exact (ih b a hb ha).symm
    | trans u v w h₁ h₂ ih₁ ih₂=>
      intro a b ha hb
      have hh:G.componentSetoid Finset.univ (G.dartPair a).1 v := by simpa only [ha] using h₁
      obtain ⟨c,hc⟩:=incident_of_component a v hh
      exact Relation.EqvGen.trans _ _ _ (ih₁ a c ha hc) (ih₂ c b hc hb)
  exact lift _ _ h a b rfl rfl

 theorem faceComponent_edge_constant : R.dualGraph.EdgeConstant Finset.univ (faceComponent R) := by
  intro e he
  change vertexComponent (G:=G) (G.src e)=vertexComponent (G.dst e)
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩)

 def dualComponentToPrimal : R.dualGraph.Components Finset.univ→G.Components Finset.univ :=
  Quotient.lift (faceComponent R) (fun f h hh=>R.dualGraph.edgeConstant_respects Finset.univ
    (faceComponent R) R.faceComponent_edge_constant hh)

 theorem dualComponentToPrimal_injective : Function.Injective R.dualComponentToPrimal := by
  intro p q hpq
  induction p using Quotient.inductionOn with | h f=>
    induction q using Quotient.inductionOn with | h h=>
      apply Quotient.sound
      change faceComponent R f=faceComponent R h at hpq
      induction f using Quotient.inductionOn with | h a=>
        induction h using Quotient.inductionOn with | h b=>
          exact R.dual_connected_of_primal a b (Quotient.exact hpq)

end PlanarHom.PlanarityLRRealization.RotationRows
