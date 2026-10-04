import PlanarHom.OracleListBatch
open PlanarHom.Complexity

def source : PromiseProblem:=⟨fun q=>q=[false],fun _=>[true,false]⟩
noncomputable def reduction :=batchReduction source (Polynomial.C 2) (by intro q h; simp [source])

def extensionA (q : Bits) : Bits:=if q=[false] then [true,false] else []
def extensionB (q : Bits) : Bits:=if q=[false] then [true,false] else List.replicate 100 true

def execute (oracle : Bits→Bits) : ℕ→PlanarHom.ListMapMachines.machine.Cfg→
    Option (PlanarHom.ListMapMachines.machine.Cfg × List Bits)
  | 0,_=>none
  | n+1,c=>if c.l.isNone then some (c,[]) else do
    let d←PlanarHom.ListMapMachines.machine.step oracle c
    let (final,trace)←execute oracle n d
    return (final,if (PlanarHom.ListMapMachines.machine.continuation c).isSome then
      PlanarHom.ListMapMachines.machine.queryWord c::trace else trace)

def test (oracle : Bits→Bits) : Bool:=
  match execute oracle 2000 (PlanarHom.ListMapMachines.machine.initial
      (BitEncoding.bits.list.encode [[false],[false],[false]])) with
  | none=>false
  | some (c,qs)=>
    let out : Bits:=c.stk .input
    out==BitEncoding.bits.list.encode [[true,false],[true,false],[true,false]] &&
      qs==[[false],[false],[false]]
#guard test extensionA
#guard test extensionB
#print axioms reduction
