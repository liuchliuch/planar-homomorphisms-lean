import PlanarHom.PlanarityFaceOrientationCorrectness
import PlanarHom.PlanarityFaceRootCache

namespace ReimplementedFaceDual
open PlanarHom.Complexity PlanarHom.PlanarityFaceCode PlanarHom.PlanarityRotationCode
open PlanarHom.MultiGraph.Kasteleyn

def bridge : MixedCode := ⟨2,[(0,(1,0))],[]⟩
def loop : MixedCode := ⟨1,[(0,(0,0))],[]⟩
def parallel : MixedCode := ⟨2,[(0,(1,0)),(0,(1,0))],[]⟩
def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def twoLoops : MixedCode := ⟨3,[(0,(0,0)),(1,(1,0))],[]⟩

theorem bridge_valid : bridge.Valid 1 1 := by simp [MixedCode.Valid,bridge]
example : (dualData bridge []).Compatible (boundaryById bridge []) := dualData_compatible bridge bridge_valid []
example : FP MixedCode.encoding logCode orientationLog := certified_orientationLog.1

 def checkedRows (g : MixedCode) : Bool :=
   let table:=cachedComputedBoundedTable g
   let log:=computeOrientation table
   table.all (fun q=>boundaryParity (logOrientation log) q.2 == faceTarget q.2)

#eval [faceId bridge [] (0,true),faceId bridge [] (0,false)]
#eval boundaryById bridge [] 0
#eval incidenceParity 0 (boundaryById bridge [] 0)
#eval [faceId loop [] (0,true),faceId loop [] (0,false)]
#eval [incidenceParity 0 (boundaryById loop [] 0),incidenceParity 0 (boundaryById loop [] 1)]
#eval [(dualData bridge []).left 20,(dualData bridge []).right 20]
#eval boundaryById bridge [] 99999999999999999999999
#eval checkedRows bridge
#eval checkedRows loop
#eval checkedRows parallel
#eval checkedRows triangle
#eval checkedRows twoLoops
end ReimplementedFaceDual
