import PlanarHom.PlanarityLRDirectMachines

namespace ReimplementedDirectRuntime
open PlanarHom.Complexity PlanarHom.PlanarityLRDirect PlanarHom.PlanarityRotationCode
open PlanarHom.NatWordComparisonMachines

def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def loopParallel : MixedCode := ⟨2,[(0,(0,0)),(0,(1,0)),(0,(1,0))],[]⟩

theorem exact_zip : indexedZip [1,2,3] [4,5]=[(1,4),(2,5)] := by decide
theorem empty_lex : ([]:List ℕ).lex [1] (fun x y=>decide (x<y))=true := rfl
theorem proper_prefix_lex : ([1,2]:List ℕ).lex [1,2,0] (fun x y=>decide (x<y))=true := by decide
theorem empty_rotation : rowNext [] (99,false)=(99,false) := by decide
theorem cyclic_rotation : rowNext [(0,true),(1,false)] (1,false)=(0,true) := by decide

example : FP (graphBitsCode.prod dartCode) dartCode (fun p=>faceStep p.1.1 p.1.2 p.2) := fp_faceStep
example (g:MixedCode) (bits:List Bool) (a b:ℕ) : (eventLE g bits a b || eventLE g bits b a)=true :=
  eventLE_total g bits a b

#eval indexedZip [1,2,3] [4,5]
#eval ([1,2]:List ℕ).lex [1,3] (fun x y=>decide (x<y))
#eval ([1,2,0]:List ℕ).lex [1,2] (fun x y=>decide (x<y))
#eval (([(0,true),(0,false),(1,true)]:List Dart).idxOf (0,false))
#eval (([(0,true),(0,false),(1,true)]:List Dart).idxOf (4,false))
#eval rowNext [] (99,false)
#eval rowNext [(0,true),(1,false)] (1,false)
#eval (List.range 3).map (directRow triangle [false,false,false])
#eval faceStep triangle [false,false,false] (0,true)
#eval faceStep triangle [false,false,false] (2,true)
#eval faceStep triangle [false,false,false] (1,false)
#eval (List.range 2).map (directRow loopParallel [false,false,false])

end ReimplementedDirectRuntime
