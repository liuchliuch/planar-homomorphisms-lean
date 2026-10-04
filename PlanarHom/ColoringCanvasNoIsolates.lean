import PlanarHom.ColoringEmitterMacroSemantics
import PlanarHom.ColoringCanvasPortCoverage
import PlanarHom.ColoringEmitterCanvas
import PlanarHom.PlanarityLRRealizationRotationSystem

noncomputable section
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree

/-- On every nonempty valid source, every literal canvas vertex has an incident
edge occurrence. Unused original variables still travel on passive wire cells. -/
theorem incident (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) (v : Vertex f) :
    ∃e,(graph f).src e=v ∨ (graph f).dst e=v := by
  cases v with
  | inl s =>
    obtain ⟨i,p,hp⟩:=canvas_boundary_port_coverage f hf hne s.1
    have hh : PortPatchAssembly.placeVertex (W:=Private f) (port f) i (.inl (p,s.2))=.inl s := by
      apply congrArg Sum.inl
      exact Prod.ext hp rfl
    obtain ⟨e,he|he⟩:=MacroSemantics.incident (canvasCell f i).shape (.inl (p,s.2))
    · refine ⟨⟨i,e⟩,Or.inl ?_⟩
      change PortPatchAssembly.placeVertex (W:=Private f) (port f) i ((LocalPatch.graph (canvasCell f i).shape).src e)=_
      rw [he,hh]
    · refine ⟨⟨i,e⟩,Or.inr ?_⟩
      change PortPatchAssembly.placeVertex (W:=Private f) (port f) i ((LocalPatch.graph (canvasCell f i).shape).dst e)=_
      rw [he,hh]
  | inr v =>
    obtain ⟨i,w⟩:=v
    obtain ⟨e,he|he⟩:=MacroSemantics.incident (canvasCell f i).shape (.inr w)
    · refine ⟨⟨i,e⟩,Or.inl ?_⟩
      change PortPatchAssembly.placeVertex (W:=Private f) (port f) i ((LocalPatch.graph (canvasCell f i).shape).src e)=_
      rw [he]
      rfl
    · refine ⟨⟨i,e⟩,Or.inr ?_⟩
      change PortPatchAssembly.placeVertex (W:=Private f) (port f) i ((LocalPatch.graph (canvasCell f i).shape).dst e)=_
      rw [he]
      rfl

theorem dart_host_surjective (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Function.Surjective (fun a : Dart (Edge f)=>((graph f).dartPair a).1) := by
  intro v
  obtain ⟨e,he|he⟩:=incident f hf hne v
  · exact ⟨(e,true),he⟩
  · exact ⟨(e,false),he⟩

end PlanarHom.ColoringEmitter.Canvas
