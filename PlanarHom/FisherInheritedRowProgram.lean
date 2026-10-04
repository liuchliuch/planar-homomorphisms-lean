import PlanarHom.FisherReferenceMachines
import PlanarHom.PlanarityRowFaceCodeProgram

/-! NEW literal numeric inherited Fisher rotations. Stage-one path/loop
addresses follow the actual internal-edge list; stage-two corner directions
track the canonical scan's local port permutation. -/
namespace PlanarHom.FisherInheritedRowCode
open Complexity PlanarityRotationCode PlanarityLRDirect
abbrev Rows := List (List Dart)

 def edgeSlots (g : MixedCode) (rows : Rows) : List (ℕ×ℕ) :=
  (List.range g.vertices).flatMap (fun v=>
    (List.range ((FisherExpansionCode.row rows v).length+3)).map (fun j=>(v,j)))
 def internalNumber (g : MixedCode) (rows : Rows) (v j : ℕ) : ℕ :=
  g.edges.length+(edgeSlots g rows).idxOf (v,j)
 def expansionRow (g : MixedCode) (rows : Rows) (w : ℕ) : List Dart :=
  let p:=(FisherExpansionCode.vertexSlots g rows).getD w (0,0)
  let v:=p.1
  let j:=p.2
  let d:=(FisherExpansionCode.row rows v).length
  if j=0 then
    [(internalNumber g rows v 0,true),(internalNumber g rows v (d+1),true),(internalNumber g rows v (d+1),false)]
  else if j=d+1 then
    [(internalNumber g rows v d,false),(internalNumber g rows v (d+2),true),(internalNumber g rows v (d+2),false)]
  else
    [(internalNumber g rows v (j-1),false),reverse ((FisherExpansionCode.row rows v).getD (j-1) (0,false)),
      (internalNumber g rows v j,true)]
 def expansionRows (g : MixedCode) : Rows :=
  (List.range (FisherExpansionCode.computed g).vertices).map
    (expansionRow g (FisherContourOrder.computedRows g))

 def cubicRow (g : MixedCode) (rows : Rows) (w : ℕ) : List Dart :=
  let v:=w/3
  let i:=w%3
  let scan:=FisherCubicCode.row g v
  let a:=reverse (scan.getD i (0,false))
  let r:=rows.getD v []
  let j:=scan.idxOf (reverse (rowNext r a))
  let k:=scan.idxOf (reverse (rowNext r.reverse a))
  [a,(g.edges.length+3*v+k,decide (FisherCubicCode.triangleSrc k=i)),
     (g.edges.length+3*v+j,decide (FisherCubicCode.triangleSrc j=i))]

 def inheritedRows (g : MixedCode) : Rows :=
  (List.range (FisherCodePipeline.code g).vertices).map
    (cubicRow (FisherCodePipeline.intermediate g) (expansionRows g))

 def orientationLog (g : MixedCode) : List ℕ :=
  PlanarityRowFaceCode.orientationLog (FisherCodePipeline.code g) (inheritedRows g)

end PlanarHom.FisherInheritedRowCode
