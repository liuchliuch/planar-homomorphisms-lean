import PlanarHom.PositiveWeightRealAvailability
import PlanarHom.WeightedRationalClosure

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PositiveWeightRemoval

private def B : Matrix (Fin 2) (Fin 2) ℚ := !![1,-2;-2,5]
private def w : Fin 2→ℚ := ![2,3]

-- Private path vertices contribute the background once, even when the
-- original edge is a loop. In particular this is14, not the unweighted5.
example : weightedChain B w 2 0 0=14 := by norm_num [weightedChain,B,w,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]
example : weightedChain B w 2 0 1= -34 := by norm_num [weightedChain,B,w,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]
example : (B^2) 0 0=5 := by norm_num [B,pow_two,Matrix.mul_apply,Fin.sum_univ_two]
example : (∑ τ : Fin 1→Fin 2,PathPower.weightedWeight 1 B w 0 0 τ)=14 := by
  rw [PathPower.sum_weightedWeight]
  norm_num [B,w,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]

private def loopGraph : MixedCode := ⟨2,[(0,0,0),(0,1,0),(0,1,0)],[(0,0),(0,0),(1,0)]⟩
private theorem loop_valid : loopGraph.Valid 2 1 := by simp [loopGraph,Valid]
example : (loopGraph.addLoops 1).edges=
    [(0,0,0),(0,1,0),(0,1,0),(1,1,1),(0,0,1)] := by decide
example : (loopGraph.addLoops 1).unaries=loopGraph.unaries := rfl
example : (addLoops 1 ⟨0,[],[]⟩)=⟨0,[],[]⟩ := by decide
example : (addLoops 1 ⟨3,[],[]⟩).edges=[(2,2,1),(1,1,1),(0,0,1)] := by decide

-- Exact background cancellation retains signed values, multiplicity and
-- original unaries. The cancellation theorem includes isolated vertices.
private def language : Fin 2→Matrix (Fin 2) (Fin 2) ℚ :=
  ![B,Matrix.diagonal (fun i=>(w i)⁻¹)]
example (U : Fin 1→Fin 2→ℚ) :
    (loopGraph.addLoops 1).evaluate (addLoops_valid (1 : Fin 2) loopGraph loop_valid) language U w =
      loopGraph.evaluate loop_valid language U (fun _=>1) := by
  have h := evaluate_addLoops (1 : Fin 2) loopGraph loop_valid language U w
  have hc : (fun i=>w i*language 1 i i)=(fun _=>1) := by
    funext i
    fin_cases i <;> norm_num [w,language]
  rw [hc] at h
  exact h

-- Selected unary occurrences each become a loop, while every other unary,
-- existing loop and repeated edge stays present.
private def unaryGraph : MixedCode := ⟨2,[(0,0,0),(0,1,0)],[(0,1),(0,1),(1,0)]⟩
example : realizeUnaryLoops 1 0 unaryGraph =
    ⟨2,[(0,0,0),(0,1,0),(0,0,0),(0,0,0)],[(1,0)]⟩ := by decide
example : realizeUnaryLoops 1 0 ⟨2,[],[(1,0)]⟩=⟨2,[],[(1,0)]⟩ := by decide
example : realizeUnaryLoops 1 0 ⟨0,[],[]⟩=⟨0,[],[]⟩ := by decide

-- Off-diagonal zeros survive rational exponent0 and negative exponents.
example (v : Fin 2→ℝ) : diagonalPower v 0 0 1=0 := by simp [diagonalPower]
example (v : Fin 2→ℝ) : diagonalPower v 0=1 := by simp [diagonalPower]
example (v : Fin 2→ℝ) : diagonalPower v (-1)=Matrix.diagonal (fun i=>(v i)⁻¹) := by
  simp [diagonalPower,Real.rpow_neg_one]
example (v : Fin 2→ℝ) : diagonalPower v (-3) 0 1=0 := by simp [diagonalPower]
example (v : Fin 2→ℝ) (hv : ∀i,0<v i) :
    ProductCompatibility.Compatible
      (fun p : Fin 2×Fin 2=>Matrix.diagonal (fun i=>(v i)⁻¹) p.1 p.2)
      (fun p=>diagonalPower v (-3/2) p.1 p.2) := diagonalPower_compatible v hv _

-- Empty input and absent selected labels make no auxiliary path vertices.
example : (stretchLabelLength ⟨0,[],[]⟩ 1 0 5)=⟨0,[],[]⟩ := by decide
example : (stretchLabelLength ⟨2,[(0,1,0)],[]⟩ 1 0 5).vertices=2 := by decide
example : (stretchLabelLength ⟨1,[(0,0,1)],[]⟩ 1 0 2).edges=[(0,1,0),(1,0,0)] := by decide

#print axioms PositiveWeightRemoval.inverseDiagonalFromRows
#print axioms PositiveWeightRemoval.removePositiveWeights
#print axioms PositiveWeightRemoval.rationalDiagonalUnaryReduction
#print axioms MixedCode.diagonalUnaryAppendReduction
