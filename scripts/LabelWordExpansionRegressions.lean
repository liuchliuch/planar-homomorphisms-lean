import PlanarHom.MagnitudeSignParallelReduction
import PlanarHom.ParallelSquareReduction

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
noncomputable section

def wordGraph : MixedCode :=
  ⟨3,[(0,0,0),(0,1,1),(0,1,1),(1,1,2)],[(0,0),(2,0)]⟩
def words : List (ℕ×List ℕ) := [(0,[1,0]),(1,[]),(2,[2,2,0])]

-- A loop expands into differently labelled loops; deleted parallel edges do
-- not delete their endpoints or the isolated vertex carrying a unary.
#guard (wordGraph.expandBinaryWords words).edges==[(0,0,1),(0,0,0),(1,1,2),(1,1,2),(1,1,0)]
#guard (wordGraph.expandBinaryWords words).vertices==3
#guard (wordGraph.expandBinaryWords words).unaries==wordGraph.unaries
#guard (wordGraph.expandBinaryWords []).edges==[]
#guard (wordGraph.expandBinaryWords []).vertices==3
#guard (wordExpansionPrepare twoFactorWord ⟨1,[(0,0,0)],[]⟩).2.map MixedCode.edges==
  [[(0,0,0),(0,0,1)]]
#guard (wordExpansionPrepare (selectedSquareWord (1 : Fin 3)) wordGraph).2.map MixedCode.edges==
  [[(0,0,0),(0,1,1),(0,1,1),(0,1,1),(0,1,1),(1,1,2)]]

noncomputable def actualTypedExpansion := (expandBinaryWordsComputer words).outputsFun wordGraph

-- Alternate natural encoding [false] decodes as label 2. The actual raw
-- compiler first normalizes it, so all three table factors are produced.
def alternateEdge : Bits := BitEncoding.frame [] ++ BitEncoding.frame [true] ++ [false]
def alternateMixed : Bits := BitEncoding.frame [false,false] ++
  BitEncoding.frame (BitEncoding.frame [true] ++ BitEncoding.frame alternateEdge) ++ BitEncoding.frame []
#guard (MixedCode.encoding.decode alternateMixed).map MixedCode.edges==some [(0,1,2)]
noncomputable def actualRawExpansion := expandBinaryWords_raw_outputs words alternateMixed
  ⟨2,[(0,1,2)],[]⟩ (by rfl)

example (basis : Module.Basis (Fin 1) ℚ ℚ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => fun _ _ : Fin 1 => (9 : ℚ))
        (fun _ : Fin 0 => fun _ => (0 : ℚ)) (fun _ => (2 : ℚ)))
      (evaluationProblem basis (fun _ : Fin 1 => fun _ _ : Fin 1 => (-3 : ℚ))
        (fun _ : Fin 0 => fun _ => (0 : ℚ)) (fun _ => (2 : ℚ))) := by
  convert squareReduction basis (fun _ _ : Fin 1 => (-3 : ℚ))
    (fun _ : Fin 0 => fun _ => (0 : ℚ)) (fun _ => (2 : ℚ)) using 1

#print axioms actualTypedExpansion
#print axioms actualRawExpansion
