import PlanarHom.ColoringFramedCanvasGraph

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree
open scoped BigOperators
namespace FramedMacro

theorem local_vertex_card (s : CellShape) :
    Fintype.card (LocalPatch.Private s)+leftCount s+3*s.outputCount+4=vertexCount s := by
  have hp:=Fintype.card_congr (LocalPatch.localVertexParts s)
  simp only [LocalPatch.Port,LocalPatch.NumericVertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hp
  have hs : s.portCount*3=leftCount s+3*s.outputCount := by cases s <;> rfl
  have hv:=vertexCount_eq s
  omega

end FramedMacro
namespace FramedCanvas

theorem vertex_card_balance (f : NumericFormula) (hf : NumericValid f) :
    Fintype.card (Vertex f)+(∑i : Canvas.Index f,FramedMacro.leftCount (canvasCell f i).shape)=
      3*f.1+∑i : Canvas.Index f,FramedMacro.vertexCount (canvasCell f i).shape := by
  have hs:=Fintype.card_congr (Canvas.signalEquiv f hf)
  simp only [Canvas.SignalAllocation,Canvas.Signal,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] at hs
  have hl : (∑i : Canvas.Index f,FramedMacro.vertexCount (canvasCell f i).shape)=
      ∑i : Canvas.Index f,(Fintype.card (LocalPatch.Private (canvasCell f i).shape)+
        FramedMacro.leftCount (canvasCell f i).shape+3*(canvasCell f i).shape.outputCount+4) :=
    Finset.sum_congr rfl (fun i _=>(FramedMacro.local_vertex_card _).symm)
  rw [hl]
  simp only [Vertex,Canvas.Vertex,Canvas.BoundaryTriple,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_sigma,Fintype.card_fin,Canvas.Private]
  rw [←hs]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  simp only [Finset.sum_mul,Canvas.Index,CanvasIndex,Fintype.card_fin]
  ring_nf
  rw [Finset.sum_mul]
  omega

theorem edge_card (f : NumericFormula) :
    Fintype.card (Edge f)=3*f.1+∑i : Canvas.Index f,FramedMacro.edgeCount (canvasCell f i).shape := by
  simp only [Edge,PatchEdge,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]

end FramedCanvas
end PlanarHom.ColoringEmitter
