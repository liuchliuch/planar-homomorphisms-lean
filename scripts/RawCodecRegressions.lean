import PlanarHom.MixedParallelMachines

/-!
Raw decoder boundary regressions. The canonicalization below is only the literal
codec operation used to test restored semantics; no FP canonicalizer is asserted.
The selected-label machine remains a typed/canonical-input theorem until that
normalization or a decoder-aware raw classifier is compiled.
-/

open PlanarHom.Complexity

#eval BitEncoding.nat.decode [false]
#eval BitEncoding.nat.encode 2
#guard BitEncoding.nat.decode [false] == some 2
#guard BitEncoding.unframe [true] == none
#guard (BitEncoding.nat.prod BitEncoding.nat).decode [true] == none
#guard BitEncoding.nat.list.decode
  (BitEncoding.frame [false] ++ BitEncoding.frame (BitEncoding.nat.encode 0)) == none

def rawGraph : Bits :=
  BitEncoding.frame [false,false] ++ BitEncoding.frame [false] ++
    BitEncoding.frames [((BitEncoding.nat.prod BitEncoding.nat).encode (0,1)),
      ((BitEncoding.nat.prod BitEncoding.nat).encode (1,0))]
#eval (GraphCode.encoding.decode rawGraph).map (fun g=>(g.vertices,g.edges))
#guard (GraphCode.encoding.decode rawGraph).map (fun g=>(g.vertices,g.edges)) == some (2,[(0,1),(1,0)])
#guard (GraphCode.encoding.decode rawGraph).map (fun g=>(GraphCode.encoding.encode g).length) == some (rawGraph.length+2)

def rawEdge : Bits := BitEncoding.frame (BitEncoding.nat.encode 0) ++
  BitEncoding.frame (BitEncoding.nat.encode 1) ++ [false]
def rawMixed : Bits := BitEncoding.frame (BitEncoding.unaryNat.encode 2) ++
  BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode 1) ++ BitEncoding.frame rawEdge) ++
  MixedCode.unaryEncoding.encode []
#guard (MixedCode.encoding.decode rawMixed).map (fun g=>(g.vertices,g.edges,g.unaries)) ==
  some (2,[(0,(1,2))],[])
#guard labelMatches 2 rawEdge == false
#guard labelMatches 2 ((BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode (0,(1,2))) == true

def rangesValid (b u : ℕ) (g : MixedCode) : Bool :=
  g.edges.all (fun e=>e.1<g.vertices && e.2.1<g.vertices && e.2.2<b) &&
  g.unaries.all (fun e=>e.1<g.vertices && e.2<u)
#guard (MixedCode.encoding.decode rawMixed).map (rangesValid 3 1) == some true
#guard (MixedCode.encoding.decode rawMixed).map (rangesValid 2 1) == some false
#guard rangesValid 3 1 ⟨2,[(2,(1,0))],[]⟩ == false
#guard rangesValid 3 1 ⟨2,[],[(0,1)]⟩ == false

def canonicalMixed : Bits := match MixedCode.encoding.decode rawMixed with
  | some g=>MixedCode.encoding.encode g | none=>[]
#guard (MixedCode.encoding.decode canonicalMixed).map (fun g=>(g.vertices,g.edges,g.unaries)) ==
  (MixedCode.encoding.decode rawMixed).map (fun g=>(g.vertices,g.edges,g.unaries))

open PlanarHom.MixedParallelMachines in
def executeCaller (selected : ℕ) : ℕ → machine.Cfg → Option machine.Cfg
  | 0,_=>none
  | n+1,c=>if c.l.isNone then some c else do
      let c'←machine.step (selectedOracle selected) c
      executeCaller selected n c'

open PlanarHom.MixedParallelMachines in
def transformedCount (raw : Bits) : Option ℕ := do
  let c←executeCaller 2 10000 (machine.initial (BitEncoding.frame (BitEncoding.unaryNat.encode 3)++raw))
  let g←MixedCode.encoding.decode (c.stk Stack.output)
  return g.edges.length

-- This explicitly records the still-open broad-raw-input boundary.
#guard transformedCount rawMixed == some 1
#guard transformedCount canonicalMixed == some 3
#eval (transformedCount rawMixed,transformedCount canonicalMixed)
