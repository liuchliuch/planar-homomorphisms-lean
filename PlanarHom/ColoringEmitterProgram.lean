import PlanarHom.ColoringEmitterMacroTables
import PlanarHom.RoutingFoldMachines

/-! NEW total occurrence-sensitive coloring emitter, including malformed source
references. Source width and graph header are independent honest unary fields. -/
noncomputable section
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram ParsimoniousNorOneInThree

abbrev EdgeCode := ℕ × (ℕ × ℕ)
structure State where
  sourceBase : ℕ
  dictionary : List ℕ
  vertices : ℕ
  edges : List EdgeCode
  deriving DecidableEq

def initial (n : ℕ) : State := ⟨n,(List.range n).map (fun i=>3*i),3*n,[]⟩

def inputRef (op : Instruction) (i : ℕ) : ℕ :=
  [op.2.1,op.2.2.1,op.2.2.2][i]?.getD 0

def localVertex (op : Instruction) (dictionary : List ℕ) (base v : ℕ) : ℕ :=
  let a := Macro.address op.1 v
  if a.1=0 then (dictionary[inputRef op a.2.1]?.getD 0)+a.2.2
  else if a.1=1 then base+3*a.2.1+a.2.2
  else base+3*Macro.outputCount op.1+a.2.1

def emitEdges (s : State) (op : Instruction) : List EdgeCode :=
  (Macro.edges op.1).map (fun e=>(localVertex op s.dictionary s.vertices e.1,
    localVertex op s.dictionary s.vertices e.2,0))

def freshDictionary (base : ℕ) (k : Kind) : List ℕ :=
  (List.range k.template.fresh).map (fun i=>if i<Macro.outputCount k then base+3*i else 0)

def step (s : State) (op : Instruction) : State :=
  ⟨s.sourceBase+op.1.template.fresh,
    s.dictionary++freshDictionary s.vertices op.1,
    s.vertices+Macro.addedVertices op.1,
    s.edges++emitEdges s op⟩

def run (n : ℕ) (ops : List Instruction) : State := ops.foldl step (initial n)
def graphOf (s : State) : MixedCode := ⟨s.vertices,s.edges,[]⟩
def compile (f : NumericFormula) : MixedCode :=
  if f.2=[] then ⟨0,[],[]⟩ else graphOf (run f.1 (PositiveRoutingCompiler.program f))
def unusedOriginal (f : NumericFormula) : ℕ := if f.2=[] then f.1 else 0

end PlanarHom.ColoringEmitter
