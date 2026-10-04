import PlanarHom.ColoringEmitterLocalPatches

/-! NEW canonical typed coloring canvas, with shared registry signal triples.
The empty source remains a separate empty numeric graph branch. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree

abbrev Index (f : NumericFormula) := CanvasIndex f
abbrev Signal (f : NumericFormula) := Boundary f
abbrev BoundaryTriple (f : NumericFormula) := Signal f × Fin 3
abbrev Port (f : NumericFormula) (i : Index f) := LocalPatch.Port (canvasCell f i).shape
abbrev Private (f : NumericFormula) (i : Index f) := LocalPatch.Private (canvasCell f i).shape
abbrev PatchEdge (f : NumericFormula) (i : Index f) := LocalPatch.Edge (canvasCell f i).shape

def patch (f : NumericFormula) (i : Index f) : MultiGraph (Port f i ⊕ Private f i) (PatchEdge f i) :=
  LocalPatch.graph (canvasCell f i).shape

def port (f : NumericFormula) (i : Index f) (p : Port f i) : BoundaryTriple f :=
  (boundaryPort f i p.1,p.2)

abbrev Vertex (f : NumericFormula) := BoundaryTriple f ⊕ Sigma (Private f)
abbrev Edge (f : NumericFormula) := Sigma (PatchEdge f)

def graph (f : NumericFormula) : MultiGraph (Vertex f) (Edge f) :=
  PortPatchAssembly.graph (patch f) (port f)

@[simp] theorem port_signal_name (f : NumericFormula) (hf : NumericValid f)
    (i : Index f) (p : Port f i) :
    boundaryName f hf (port f i p).1=((canvasCell f i).portData p.1).1 :=
  boundaryName_port f hf i p.1

end PlanarHom.ColoringEmitter.Canvas
