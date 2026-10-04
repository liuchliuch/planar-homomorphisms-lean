import PlanarHom.PlanarityFaceRootMachines
import PlanarHom.PlanarityFaceRoots
import PlanarHom.PlanarityFaceCache

/-! NEW exact finite successor caching for the component-root/table/log program. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRConstraints

 def cachedBoundedTable (g : MixedCode) (bits : List Bool) : List MultiGraph.Kasteleyn.RawFace :=
   let ts:=faceTransitions g bits
   let f:=transition ts
   let rs:=finiteRepresentatives (allDarts g) f (2*g.edges.length)
   let root := fun a=> (rs.filter (fun b=>decide
     (componentRoot g (host g b)=componentRoot g (host g a)))).headD a
   (rs.zipIdx.filter (fun p=>decide (root p.1≠p.1))).map
     (fun p=>(p.2,finiteBoundary f (2*g.edges.length) p.1))
 def cachedComputedBoundedTable (g : MixedCode) := cachedBoundedTable g (decideAligned g).2
 def cachedOrientationLog (g : MixedCode) := MultiGraph.Kasteleyn.computeOrientation (cachedComputedBoundedTable g)

 theorem cachedBoundedTable_eq (g : MixedCode) (bits : List Bool) :
    cachedBoundedTable g bits=boundedTable g bits := by
  simp only [cachedBoundedTable,finiteRepresentatives_eq,boundedTable,rootRepresentative]
  apply List.map_congr_left
  intro p hp
  have ha:=(List.mem_filter.mp (List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hp).1)).1
  rw [finiteBoundary_eq g bits ((mem_allDarts g p.1).mp ha)]

 theorem cachedComputedBoundedTable_eq (g : MixedCode) : cachedComputedBoundedTable g=computedBoundedTable g :=
   cachedBoundedTable_eq g _

 theorem cachedOrientationLog_eq (g : MixedCode) : cachedOrientationLog g=orientationLog g := by
   simp only [cachedOrientationLog,cachedComputedBoundedTable_eq,orientationLog]

 theorem fp_cachedOrientationLog : FP MixedCode.encoding MultiGraph.Kasteleyn.logCode cachedOrientationLog :=
   fp_orientationLog.congr (fun g=>(cachedOrientationLog_eq g).symm)

end PlanarHom.PlanarityFaceCode
