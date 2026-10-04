import PlanarHom.NatCanonicalizationMachine
open PlanarHom.Complexity PlanarHom.NatCanonicalizationMachine Turing

def runCanon : ℕ→machine.Cfg→Option machine.Cfg
  | 0,_=>none
  | n+1,c=>if c.l.isNone then some c else do
    let d←machine.step c
    runCanon n d

def eqBits (a b : Bits) : Bool:=a==b

def testCanon (xs : Bits) : Bool:=
  match runCanon (2*xs.length+6) (initList machine xs) with
  | none=>false
  | some c=>eqBits (c.stk .input) (BitEncoding.nat.encode (Computability.decodeNat xs)) &&
      eqBits (c.stk .buffer) []

def words : ℕ→List Bits
  | 0=>[[]]
  | n+1=>(words n).flatMap (fun w=>[false::w,true::w])
#guard canonical [false]==[false,true]
#guard canonical [true,false]==[true,false,true]
#guard canonical [false,false]==[false,false,true]
#guard canonical []==[]
#guard (List.range 9).all (fun n=>(words n).all testCanon)
#eval (List.range 9).all (fun n=>(words n).all testCanon)
