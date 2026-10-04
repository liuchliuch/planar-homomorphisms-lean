import PlanarHom.PlanarityLRDirectMachines
import PlanarHom.OccurrenceKasteleynOrientationLog

/-! NEW literal two-stage occurrence Fisher compiler. All lists and natural
addresses are executable; validity, correspondence and encoded runtime are
proved in separate modules. No geometric witness is a program input. -/
namespace PlanarHom.FisherContourOrder
open Complexity PlanarityLRDirect PlanarityLRConstraints PlanarityRotationCode
abbrev Rows := List (List (ℕ×Bool))
/-- Fisher endpoint tags are the reversals of Kasteleyn host-dart tags. -/
def computedRows (g : MixedCode) : Rows :=
  (List.range g.vertices).map (fun v=>(directRow g (decideAligned g).2 v).map reverse)
end PlanarHom.FisherContourOrder

namespace PlanarHom.FisherExpansionCode
open Complexity
abbrev Rows := FisherContourOrder.Rows

def row (rows : Rows) (v : ℕ) : List (ℕ×Bool) := rows.getD v []

def vertexSlots (g : MixedCode) (rows : Rows) : List (ℕ×ℕ) :=
  (List.range g.vertices).flatMap (fun v=>(List.range ((row rows v).length+2)).map (fun j=>(v,j)))

def vertexNumber (g : MixedCode) (rows : Rows) (v j : ℕ) : ℕ := (vertexSlots g rows).idxOf (v,j)

def endpoint (g : MixedCode) (a : ℕ×Bool) : ℕ :=
  let e:=g.edges.getD a.1 (0,0,0)
  if a.2 then e.2.1 else e.1

def portNumber (g : MixedCode) (rows : Rows) (a : ℕ×Bool) : ℕ :=
  let v:=endpoint g a
  vertexNumber g rows v ((row rows v).idxOf a+1)

def externalEdges (g : MixedCode) (rows : Rows) : List (ℕ×(ℕ×ℕ)) :=
  (List.range g.edges.length).map (fun e=>(portNumber g rows (e,false),portNumber g rows (e,true),0))

def localEdges (g : MixedCode) (rows : Rows) (v : ℕ) : List (ℕ×(ℕ×ℕ)) :=
  let d:=(row rows v).length
  (List.range (d+1)).map (fun j=>(vertexNumber g rows v j,vertexNumber g rows v (j+1),0)) ++
    [(vertexNumber g rows v 0,vertexNumber g rows v 0,0),
     (vertexNumber g rows v (d+1),vertexNumber g rows v (d+1),0)]

def internalEdges (g : MixedCode) (rows : Rows) : List (ℕ×(ℕ×ℕ)) :=
  (List.range g.vertices).flatMap (localEdges g rows)

def code (g : MixedCode) (rows : Rows) : MixedCode :=
  ⟨(vertexSlots g rows).length,externalEdges g rows++internalEdges g rows,[]⟩

def computed (g : MixedCode) : MixedCode := code g (FisherContourOrder.computedRows g)

def weights {K : Type*} [Zero K] [One K] (g : MixedCode) (rows : Rows) (x : List K) : List K :=
  (List.range g.edges.length).map (fun e=>x.getD e 0) ++ (internalEdges g rows).map (fun _=>1)
end PlanarHom.FisherExpansionCode

namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph.Kasteleyn

def row (g : MixedCode) (v : ℕ) : List (ℕ×Bool) :=
  (g.edges.zipIdx).flatMap (fun q=>
    (if q.1.1=v then [(q.2,false)] else []) ++ (if q.1.2.1=v then [(q.2,true)] else []))

def portNumber (g : MixedCode) (a : ℕ×Bool) : ℕ :=
  let v:=FisherExpansionCode.endpoint g a
  3*v+(row g v).idxOf a

def triangleSrc (j : ℕ) : ℕ := if j=0 then 1 else if j=1 then 2 else 0
def triangleDst (j : ℕ) : ℕ := if j=0 then 2 else if j=1 then 0 else 1

def externalEdges (g : MixedCode) : List (ℕ×(ℕ×ℕ)) :=
  (List.range g.edges.length).map (fun e=>(portNumber g (e,false),portNumber g (e,true),0))

def internalEdges (g : MixedCode) : List (ℕ×(ℕ×ℕ)) :=
  (List.range g.vertices).flatMap (fun v=>(List.range 3).map
    (fun j=>(3*v+triangleSrc j,3*v+triangleDst j,0)))

def code (g : MixedCode) : MixedCode := ⟨3*g.vertices,externalEdges g++internalEdges g,[]⟩

def portWeight {K : Type*} [Zero K] [One K] (x : List K) (a : ℕ×Bool) : K :=
  if a.2 then 1 else x.getD a.1 0

def weights {K : Type*} [Mul K] [Zero K] [One K] (g : MixedCode) (x : List K) : List K :=
  (List.range g.edges.length).map (fun _=>1) ++ (List.range g.vertices).flatMap
    (fun v=>(List.range 3).map (fun j=>portWeight x ((row g v).getD (triangleSrc j) (0,false))*
      portWeight x ((row g v).getD (triangleDst j) (0,false))))

def referenceLower (g : MixedCode) (e : ℕ) : ℕ := min (portNumber g (e,false)) (portNumber g (e,true))
def referenceUpper (g : MixedCode) (e : ℕ) : ℕ := max (portNumber g (e,false)) (portNumber g (e,true))
def referenceCross (g : MixedCode) (e f : ℕ) : Bool :=
  decide (referenceLower g e<referenceLower g f ∧ referenceLower g f<referenceUpper g e ∧ referenceUpper g e<referenceUpper g f)

def referenceEdgeSign {K : Type*} [CommRing K] (g : MixedCode) (log : List ℕ) (e : ℕ) : K :=
  let s:K:=if logOrientation log e then 1 else -1
  if portNumber g (e,false)<portNumber g (e,true) then s else -s

def referenceSign {K : Type*} [CommRing K] (g : MixedCode) (log : List ℕ) : K :=
  ((List.range g.edges.length).map (referenceEdgeSign g log)).prod *
    ((List.range g.edges.length).flatMap (fun e=>(List.range g.edges.length).map
      (fun f=>if referenceCross g e f then (-1:K) else 1))).prod
end PlanarHom.FisherCubicCode

namespace PlanarHom.FisherCodePipeline
open Complexity

def intermediate (g : MixedCode) : MixedCode := FisherExpansionCode.computed g
def code (g : MixedCode) : MixedCode := FisherCubicCode.code (intermediate g)

def isingWeights {K : Type*} [Field K] (ρ : K) (g : MixedCode) : List K :=
  List.replicate g.edges.length ((1-ρ)/(1+ρ))

def isingData {K : Type*} [Field K] (ρ : K) (g : MixedCode) : MixedCode×List K :=
  (code g,FisherCubicCode.weights (intermediate g)
    (FisherExpansionCode.weights g (FisherContourOrder.computedRows g) (isingWeights ρ g)))
end PlanarHom.FisherCodePipeline
