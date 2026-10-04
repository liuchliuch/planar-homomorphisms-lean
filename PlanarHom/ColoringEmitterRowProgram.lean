import PlanarHom.ColoringEmitterMachines

/-! NEW literal numeric row program. Each local fixed-table row is lifted by
the exact emitted-edge prefix length; cells are read in reverse order. -/
namespace PlanarHom.ColoringEmitterRows
open Complexity PositiveBlockProgram ParsimoniousNorOneInThree ColoringEmitter
abbrev Dart := ℕ×Bool
abbrev RowTable := Kind→List (List Dart)
abbrev dartCode := BitEncoding.nat.prod BitEncoding.bool
abbrev rowsCode := dartCode.list.list

def cellRow (table : RowTable) (s : State) (op : Instruction) (v : ℕ) : List Dart :=
  (List.range (Macro.vertexCount op.1)).flatMap (fun w=>
    if localVertex op s.dictionary s.vertices w=v then
      ((table op.1)[w]?.getD []).map (fun a=>(s.edges.length+a.1,a.2)) else [])

def programRow (table : RowTable) (n : ℕ) (ops : List Instruction) (v : ℕ) : List Dart :=
  (List.range ops.length).reverse.flatMap (fun i=>
    cellRow table (run n (ops.take i)) (ops[i]?.getD (.wire,0,0,0)) v)

def rows (table : RowTable) (f : NumericFormula) : List (List Dart) :=
  (List.range (compile f).vertices).map (programRow table f.1 (PositiveRoutingCompiler.program f))
end PlanarHom.ColoringEmitterRows
