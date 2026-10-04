import PlanarHom.ColoringFramedCanvasRetention
import PlanarHom.PottsRandomCluster

/-! The selected original edge occurrences retain exactly the source graph
components, plus one isolated component for each frame-only corner. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree

abbrev Corner (f : NumericFormula) := Canvas.Index f×Fin 4

def selectedEdges (f : NumericFormula) : Finset (Edge f) := Finset.univ.filter (fun e=>keepEdge f e)

theorem oldEdge_mem (f : NumericFormula) (e : Canvas.Edge f) : oldEdge f e∈selectedEdges f := by
  obtain ⟨i,e⟩:=e
  simp only [selectedEdges,Finset.mem_filter,Finset.mem_univ,true_and,oldEdge,keepEdge,
    FramedMacro.oldEdge,Fin.coe_castLE,decide_eq_true_eq]
  exact e.isLt

theorem selectedEdge_origin (f : NumericFormula) (e : Edge f) (he : e∈selectedEdges f) :
    ∃a : Canvas.Edge f,oldEdge f a=e := by
  have hh : keepEdge f e=true := (Finset.mem_filter.mp he).2
  cases e with
  | inl e => cases hh
  | inr e =>
    obtain ⟨i,e⟩:=e
    have hb : e.val<(Macro.edges (canvasCell f i).shape.kind).length := of_decide_eq_true hh
    exact ⟨⟨i,⟨e.val,hb⟩⟩,rfl⟩

theorem lift_source_connected (f : NumericFormula) {u v : Canvas.Vertex f}
    (h : (Canvas.graph f).componentSetoid Finset.univ u v) :
    (graph f).componentSetoid (selectedEdges f) (.inl u) (.inl v) := by
  induction h with
  | rel u v h =>
    obtain ⟨e,_,hs,ht⟩:=h
    exact Relation.EqvGen.rel _ _ ⟨oldEdge f e,oldEdge_mem f e,by rw [old_source,hs],by rw [old_target,ht]⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

def componentLabel (f : NumericFormula) : Vertex f→(Canvas.graph f).Components Finset.univ⊕Corner f
  | .inl v => .inl (Quotient.mk _ v)
  | .inr c => .inr c

theorem componentLabel_constant (f : NumericFormula) :
    (graph f).EdgeConstant (selectedEdges f) (componentLabel f) := by
  intro e he
  obtain ⟨a,rfl⟩:=selectedEdge_origin f e he
  rw [old_source,old_target]
  apply congrArg Sum.inl
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨a,Finset.mem_univ _,rfl,rfl⟩)

def sourceComponentLift (f : NumericFormula) : (Canvas.graph f).Components Finset.univ→
    (graph f).Components (selectedEdges f) := Quotient.lift
  (fun v=>Quotient.mk _ (.inl v)) (fun _ _ h=>Quotient.sound (lift_source_connected f h))

def selectedComponentEquiv (f : NumericFormula) :
    (graph f).Components (selectedEdges f)≃((Canvas.graph f).Components Finset.univ⊕Corner f) where
  toFun := Quotient.lift (componentLabel f)
    (fun _ _ h=>(graph f).edgeConstant_respects _ _ (componentLabel_constant f) h)
  invFun
    | .inl c => sourceComponentLift f c
    | .inr c => Quotient.mk _ (.inr c)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h v => cases v <;> rfl
  right_inv c := by
    cases c with
    | inl c => induction c using Quotient.inductionOn with | h v => rfl
    | inr c => rfl

theorem selected_componentCount (f : NumericFormula) :
    (graph f).componentCount (selectedEdges f)=(Canvas.graph f).componentCount Finset.univ+Fintype.card (Corner f) := by
  exact (Fintype.card_congr (selectedComponentEquiv f)).trans (Fintype.card_sum)

end PlanarHom.ColoringEmitter.FramedCanvas
