import PlanarHom.GraphComponentMachines
import PlanarHom.PlanarityRowFaceCodeProgram

/-! NEW literal supplied-row component compiler. The edge-index registry has
exactly GraphComponentCode.extract's stable retained-occurrence order. -/
namespace PlanarHom.SurfaceComponentCode
open Complexity PlanarityRowFaceCode

def edgeIds (g : MixedCode) (xs : List ℕ) : List ℕ :=
  (g.edges.zipIdx.filter (fun p => GraphComponentCode.edgeInside xs p.1)).map Prod.snd

def extractRows (g : MixedCode) (rows : Rows) (xs : List ℕ) : Rows :=
  xs.map (fun v => (rows.getD v []).map (fun a => ((edgeIds g xs).idxOf a.1,a.2)))

def extract (g : MixedCode) (rows : Rows) (xs : List ℕ) : MixedCode×Rows :=
  (GraphComponentCode.extract g xs,extractRows g rows xs)

def components (g : MixedCode) (rows : Rows) : List (MixedCode×Rows) :=
  (GraphComponentCode.parts g).map (extract g rows)

end PlanarHom.SurfaceComponentCode
