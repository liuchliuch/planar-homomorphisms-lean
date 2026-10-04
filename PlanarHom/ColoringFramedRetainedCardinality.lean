import PlanarHom.ColoringFramedSelectedComponents

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn ParsimoniousNorOneInThree

theorem oldEdge_injective (f : NumericFormula) : Function.Injective (oldEdge f) := by
  intro a b h
  have hh : oldDart f (a,true)=oldDart f (b,true) := Prod.ext h rfl
  exact congrArg Prod.fst (oldDart_injective f hh)

def selectedEdgeEquiv (f : NumericFormula) : Canvas.Edge f≃(selectedEdges f) :=
  Equiv.ofBijective (fun e=>⟨oldEdge f e,oldEdge_mem f e⟩) (by
    constructor
    · intro a b h
      exact oldEdge_injective f (congrArg Subtype.val h)
    · intro e
      obtain ⟨a,ha⟩:=selectedEdge_origin f e.val e.property
      exact ⟨a,Subtype.ext ha⟩)

theorem selectedEdges_card (f : NumericFormula) : (selectedEdges f).card=Fintype.card (Canvas.Edge f) := by
  rw [←Fintype.card_coe]
  exact (Fintype.card_congr (selectedEdgeEquiv f)).symm

theorem vertex_card_split (f : NumericFormula) :
    Fintype.card (Vertex f)=Fintype.card (Canvas.Vertex f)+Fintype.card (Corner f) := Fintype.card_sum

end PlanarHom.ColoringEmitter.FramedCanvas
