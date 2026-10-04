import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.ListMutationMachines
open PlanarHom.Complexity Turing

def source : PromiseProblem:=⟨fun q=>q=[false],fun _=>[true]⟩
def target : PromiseProblem:=⟨fun q=>q=[false],fun _=>BitEncoding.bits.list.encode [[true]]⟩

noncomputable def regression : PromisePolyTimeTuringReduction target source:=by
  have singleton : FP BitEncoding.bits BitEncoding.bits.list (fun x=>[x]):=
    ((fp_id BitEncoding.bits).pair (fp_const BitEncoding.bits BitEncoding.bits.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons BitEncoding.bits)
  have prep : FP BitEncoding.bits (BitEncoding.bits.prod BitEncoding.bits.list) (fun x=>(x,[x])):=
    (fp_id BitEncoding.bits).pair singleton
  exact nonadaptiveReduction BitEncoding.bits BitEncoding.bits BitEncoding.bits BitEncoding.bits BitEncoding.bits.list
    target source (fun x=>(x,[x])) (fun _=>[true]) Prod.snd (Classical.choice prep)
    (PairProjectionMachines.sndEncodingComputer BitEncoding.bits BitEncoding.bits.list)
    (fun raw _=>raw) (fun _ _=>rfl)
    (by intro raw h q hq; have he:q=raw:=List.mem_singleton.mp hq; simpa only [he] using h)
    (fun _ _=>rfl) (fun _ _=>rfl) (Polynomial.C 1) (by intro q h; simp [source])

def extension (q : Bits) : Bits:=if q=[false] then [true] else List.replicate 100 false

theorem concrete_run : ∃steps cost qs,regression.machine.Run extension
    (regression.machine.initial [false])
    (regression.machine.final (BitEncoding.bits.list.encode [[true]])) steps cost qs ∧
      cost≤regression.time.eval 1 ∧ ∀q a,(q,a)∈qs→q=[false]:=by
  exact regression.computes extension (by intro q h; change q=[false] at h; simp [extension,source,h])
    [false] rfl

#print axioms regression
#print axioms concrete_run

open PlanarHom.ContextualOracleBatch in
def execute : ℕ→machine.Cfg→Option machine.Cfg
  | 0,_=>none
  | n+1,c=>if c.l.isNone then some c else do
    let d←machine.step extension c
    execute n d

open PlanarHom.ContextualOracleBatch in
def testContext (ctx : Bits) (queries : List Bits) : Bool:=
  match execute 10000 (machine.initial (BitEncoding.frame ctx++BitEncoding.bits.list.encode queries)) with
  | none=>false
  | some c=>
    let out : Bits:=c.stk (.inr .input)
    let saved : Bits:=c.stk (.inl ())
    out==(BitEncoding.frame ctx++BitEncoding.bits.list.encode (queries.map extension)) && saved==[]
#guard testContext [] []
#guard testContext [false,true,false] [[false],[false]]
#guard testContext [true] [[false],[]]
