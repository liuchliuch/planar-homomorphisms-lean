import PlanarHom.Corollary32Realization

open PlanarHom PlanarHom.ProductCompatibility PlanarHom.Corollary32
noncomputable section

def signedAlphabet (i : Fin 5) : ℝ :=
  if i.val = 0 then 0 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then -3 else 3

-- Minimum means minimum NONZERO magnitude, not minimum signed entry.
example : extremalMask (fun i => |signedAlphabet i|) 2 0 = 0 := by
  norm_num [extremalMask,signedAlphabet]
example : extremalMask (fun i => |signedAlphabet i|) 2 1 = 1 := by
  norm_num [extremalMask,signedAlphabet]
example : extremalMask (fun i => |signedAlphabet i|) 2 3 = 0 := by
  norm_num [extremalMask,signedAlphabet]
example : extremalMask (fun i => |signedAlphabet i|) 3 3 = 1 := by
  norm_num [extremalMask,signedAlphabet]
example : extremalMask (fun i => |signedAlphabet i|) 3 4 = 1 := by
  norm_num [extremalMask,signedAlphabet]

-- Equal signed products may use different signs in the original factors.
example : (([1,3] : List (Fin 5)).map signedAlphabet).prod =
    (([2,4] : List (Fin 5)).map signedAlphabet).prod := by norm_num [signedAlphabet]
example : (([1,4] : List (Fin 5)).map (fun i => Real.sign (signedAlphabet i))).prod = -1 := by
  change Real.sign (-2) * (Real.sign 3 * 1) = -1
  norm_num [Real.sign]
example : supportTransform (fun _ : Fin 1 => (0 : ℝ)) 0 = 0 := by simp [supportTransform]
example : |(0 : ℝ)| * Real.sign 0 = 0 := by simp

#print axioms Corollary32.mixed_equivalence
#print axioms Corollary32.support_chains
#print axioms Corollary32.joint_extremal_transforms
#print axioms Corollary32.square_planar_gadget
#print axioms Corollary32.evaluate_square_expansion

-- Two parallel loops retain the second, isolated vertex and both weights.
def doubledLoopWithIsolate : MultiGraph (Fin 2) (Fin 2) := ⟨fun _ => 0, fun _ => 0⟩
def singleLoopWithIsolate : MultiGraph (Fin 2) (Fin 1) := ⟨fun _ => 0, fun _ => 0⟩
example : doubledLoopWithIsolate.partition (fun _ _ : Fin 1 => (-3 : ℚ)) (fun _ => (2 : ℚ)) = 36 := by
  norm_num [MultiGraph.partition, MultiGraph.assignmentWeight, doubledLoopWithIsolate]
example : singleLoopWithIsolate.partition (fun _ _ : Fin 1 => (9 : ℚ)) (fun _ => (2 : ℚ)) = 36 := by
  norm_num [MultiGraph.partition, MultiGraph.assignmentWeight, singleLoopWithIsolate]
