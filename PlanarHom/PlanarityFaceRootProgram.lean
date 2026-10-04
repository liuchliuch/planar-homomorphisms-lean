import PlanarHom.PlanarityFaceCodeMachines
import PlanarHom.PlanarityLRComponents

/-! NEW reconstruction. Omit the first represented face in each literal DFS
component. This is a combinatorial root convention, not an exterior-face oracle. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRConstraints

 def rootRepresentative (g : MixedCode) (bits : List Bool) (a : Dart) : Dart :=
   ((representatives g bits).filter (fun b=>decide
     (componentRoot g (host g b)=componentRoot g (host g a)))).headD a

 def boundedTable (g : MixedCode) (bits : List Bool) : List MultiGraph.Kasteleyn.RawFace :=
   ((representatives g bits).zipIdx.filter
     (fun p=>decide (rootRepresentative g bits p.1≠p.1))).map
       (fun p=>(p.2,boundary g bits p.1))

 def computedBoundedTable (g : MixedCode) : List MultiGraph.Kasteleyn.RawFace :=
   boundedTable g (decideAligned g).2

 def orientationLog (g : MixedCode) : List ℕ :=
   MultiGraph.Kasteleyn.computeOrientation (computedBoundedTable g)

 theorem boundedTable_sublist (g : MixedCode) (bits : List Bool) :
    (boundedTable g bits).Sublist (fullTable g bits) :=
   (List.filter_sublist (l := (representatives g bits).zipIdx)).map _

 theorem boundedTable_length (g : MixedCode) (bits : List Bool) :
    (boundedTable g bits).length≤2*g.edges.length :=
   (boundedTable_sublist g bits).length_le.trans (fullTable_length g bits)

 theorem orientationLog_length (g : MixedCode) : (orientationLog g).length≤2*g.edges.length :=
   (MultiGraph.Kasteleyn.computeOrientation_length_le _).trans (boundedTable_length g _)

end PlanarHom.PlanarityFaceCode
