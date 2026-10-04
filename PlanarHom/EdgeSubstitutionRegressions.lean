import PlanarHom.EdgeSubstitutionSemantics
import PlanarHom.EdgeSubstitutionRawMachine

/-! NEW regression checks for literal occurrences and the exact semantic/raw bridges. -/
namespace PlanarHom.EdgeSubstitution.Regressions
open Complexity FixedGadgetNetwork

example (ts : List Template) : substitute ts ⟨0,[],[]⟩=⟨0,[],[]⟩ := rfl
example (ts : List Template) : substitute ts ⟨5,[],[(2,7),(2,7)]⟩=⟨5,[],[(2,7),(2,7)]⟩ := rfl
example : substitute [] ⟨2,[(0,1,17)],[(1,2)]⟩=⟨2,[],[(1,2)]⟩ := by decide

private def pathTemplate : Template := ⟨2,1,[(0,2,0),(2,1,0)],[(2,0)]⟩
private def loopHost : MixedCode := ⟨3,[(0,1,0),(0,0,0),(0,1,0)],[(2,0),(2,0),(0,0)]⟩

-- A loop, repeated edges and unaries, and the isolated old vertex 2 survive.
-- Every edge occurrence gets a separate private block in its original order.
example : substitute [pathTemplate] loopHost =
    ⟨6,[(0,3,0),(3,1,0),(0,4,0),(4,0,0),(0,5,0),(5,1,0)],
      [(2,0),(2,0),(0,0),(3,0),(4,0),(5,0)]⟩ := by decide

private theorem path_valid : pathTemplate.code.Valid 1 1 := by simp [pathTemplate,Template.code,MixedCode.Valid]
private theorem host_valid : loopHost.Valid 1 1 := by simp [loopHost,MixedCode.Valid]

example {C R : Type} [Fintype C] [CommSemiring R]
    (M : Fin 1→Matrix C C R) (U : Fin 1→C→R) :
    (substitute [pathTemplate] loopHost).evaluate
      (substitute_valid [pathTemplate] (by simpa using path_valid) (by simp [pathTemplate])
        loopHost host_valid) M U (fun _=>1) =
      loopHost.evaluate host_valid (interactions [pathTemplate] M U) U (fun _=>1) :=
  evaluate_substitute [pathTemplate] (by simpa using path_valid) (by simp [pathTemplate]) loopHost host_valid M U

-- No private vertices: two terminal unary occurrences can map to one loop vertex.
example : substitute [⟨2,0,[],[(0,0),(1,0)]⟩] ⟨1,[(0,0,0)],[]⟩ =
    ⟨1,[],[(0,0),(0,0)]⟩ := by decide

-- A genuine noncanonical raw word encoding one isolated vertex.
private def noncanonicalWord : Bits :=
  BitEncoding.frame [false] ++
    (BitEncoding.frame (edgeItemEncoding.list.encode []) ++ unaryItemEncoding.list.encode [])

private theorem noncanonical_decodes : MixedCode.encoding.decode noncanonicalWord=some ⟨1,[],[]⟩ := by
  simp [noncanonicalWord,MixedCode.encoding,BitEncoding.retract,
    edgeItemEncoding,unaryItemEncoding,BitEncoding.prod,BitEncoding.unaryNat,BitEncoding.decode_encode]
example : noncanonicalWord≠MixedCode.encoding.encode ⟨1,[],[]⟩ := by decide
noncomputable def noncanonicalExecution (ts : List Template) :=
  substitute_raw_outputs ts noncanonicalWord ⟨1,[],[]⟩ noncanonical_decodes
example : MixedCode.encoding.decode []=none := by decide
example (ts : List Template) : FP MixedCode.encoding MixedCode.encoding (substitute ts) := fp_substitute ts

end PlanarHom.EdgeSubstitution.Regressions
