import PlanarHom.RootedRealTractability

open PlanarHom PlanarHom.Complexity
open RootedCodeMachines
noncomputable section

-- A root loop and two repeated root-to-new-vertex occurrences remain distinct.
def testGadget : RootedGraph (Fin 1) (Fin 3) where
  src _ := .inl PUnit.unit
  dst e := if e.val=0 then .inl PUnit.unit else .inr 0

def testGraph : MixedCode := ⟨3,[(0,0,2),(1,2,1)],[(2,0),(2,0)]⟩
#guard attach testGadget 0 (2,testGraph) ==
  ⟨4,[(0,0,2),(1,2,1),(2,2,0),(2,3,0),(2,3,0)],[(2,0),(2,0)]⟩

-- The raw root word [false] means 2 in the pinned natural decoder.
def alternateRootWord : Bits := BitEncoding.frame [false] ++ MixedCode.encoding.encode testGraph
theorem alternateDecode : inputEncoding.decode alternateRootWord = some (2,testGraph) := by
  change (BitEncoding.nat.prod MixedCode.encoding).decode
    (BitEncoding.frame [false] ++ MixedCode.encoding.encode testGraph) = _
  have hn : BitEncoding.nat.decode [false] = some 2 := by decide
  change Option.bind (BitEncoding.nat.decode [false]) (fun xa =>
    Option.bind (MixedCode.encoding.decode (MixedCode.encoding.encode testGraph))
      (fun xb => some (xa,xb))) = _
  rw [hn,MixedCode.encoding.decode_encode]
  rfl

def alternateRootExecution := raw_outputs testGadget 0 alternateRootWord 2 testGraph alternateDecode
#print axioms alternateRootExecution

-- A raw malformed frame is excluded by the actual successful-decoding promise.
example : inputEncoding.decode [true] = none := by decide
example : ¬ RootedRestriction.rootValid [true] := by
  rintro ⟨p,h,_⟩
  have hn : inputEncoding.decode [true] = none := by decide
  rw [hn] at h
  contradiction

-- Out-of-range roots are rejected even when the underlying graph is valid.
def singletonCode : MixedCode := ⟨1,[],[]⟩
example : ¬ RootedRestriction.rootValid (inputEncoding.encode (1,singletonCode)) := by
  rintro ⟨p,h,hp,hr⟩
  rw [inputEncoding.decode_encode] at h
  cases Option.some.inj h
  exact Nat.lt_irrefl 1 hr

-- Empty and full fixed color restrictions have the expected exact values.
example {V E C : Type} [Fintype V] [Fintype E] [Fintype C]
    (G : RootedGraph V E) (M : Matrix C C ℚ) (w : C → ℚ) :
    RootedGraph.restricted G M w ∅ = 0 := by simp [RootedGraph.restricted]
example {V E C : Type} [Fintype V] [Fintype E] [Fintype C]
    (G : RootedGraph V E) (M : Matrix C C ℚ) (w : C → ℚ) :
    RootedGraph.restricted G M w Set.univ = G.partition M w := by
  rw [RootedGraph.partition_eq_sum_signature]
  simp [RootedGraph.restricted]

-- Fixed coefficient recovery retains signs and includes the empty query batch.
#guard RootedRestriction.recover (fun i : Fin 2 => if i.val=0 then (2:ℚ) else -3)
  (0,[5,7]) == -11
#guard RootedRestriction.recover (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℚ) (0,[]) == 0

#print axioms RootedRestriction.exists_fixed_planar_queries
#print axioms MultiGraph.Planar.attachRooted
#print axioms RootedRestriction.rootReduction
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma35_root

#print axioms AlgebraicProductInterpolation.RealLanguage.exists_real_root_formula
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma35_component
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma35_inFP
