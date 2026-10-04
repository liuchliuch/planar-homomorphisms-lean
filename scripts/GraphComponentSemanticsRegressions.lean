import PlanarHom.GraphComponentReduction

open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.GraphComponentCode
noncomputable section
open Classical

-- The empty graph makes an empty batch and has partition value one, even if
-- the color set itself is empty.
example {C R : Type} [Fintype C] [CommSemiring R] {b u : ℕ}
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R) :
    MixedCode.evaluate ⟨0,[],[]⟩ (by simp [MixedCode.Valid]) M U w = 1 := by
  rw [evaluate_components]
  have he : components ⟨0,[],[]⟩ = [] := by decide
  simp only [he,List.map_nil,List.prod_nil]

private def repeated : MixedCode :=
  ⟨2,[(0,0,0),(0,0,0)],[(0,0),(0,0),(1,0)]⟩

private theorem repeated_valid : repeated.Valid 1 1 := by
  simp [repeated,MixedCode.Valid]

-- Equal loops and unary occurrences are kept as separate multiplicative factors.
example : components repeated =
    [⟨1,[(0,0,0),(0,0,0)],[(0,0),(0,0)]⟩,⟨1,[],[(0,0)]⟩] := by decide

example {C R : Type} [Fintype C] [CommSemiring R]
    (M : Fin 1 → Matrix C C R) (U : Fin 1 → C → R) (w : C → R) :
    repeated.evaluate repeated_valid M U w =
      MixedCode.totalEvaluation M U w ⟨1,[(0,0,0),(0,0,0)],[(0,0),(0,0)]⟩ *
      MixedCode.totalEvaluation M U w ⟨1,[],[(0,0)]⟩ := by
  rw [evaluate_components]
  have he : components repeated =
    [⟨1,[(0,0,0),(0,0,0)],[(0,0),(0,0)]⟩,⟨1,[],[(0,0)]⟩] := by decide
  simp only [he,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

-- Three isolated vertices each independently choose either of two colors.
example : MixedCode.evaluate ⟨3,[],[]⟩ (by simp [MixedCode.Valid])
    (fun (_ : Fin 1) (_ _ : Fin 2) => (1:ℚ))
    (fun (_ : Fin 1) (_ : Fin 2) => (1:ℚ)) (fun _ => 1) = 8 := by
  norm_num [MixedCode.evaluate]

-- Numerical regression: two loop factors, three unary factors, and two
-- background factors all contribute with their original multiplicities.
example : repeated.evaluate repeated_valid
    (fun (_ : Fin 1) (_ _ : Fin 1) => (3:ℚ))
    (fun (_ : Fin 1) (_ : Fin 1) => (5:ℚ)) (fun _ => 2) = 4500 := by
  norm_num [MixedCode.evaluate,repeated,MixedCode.binaryValue,MixedCode.unaryValue,
    Fin.prod_univ_two]

-- The factorization theorem applies with negative matrix entries and exact
-- cancellation; positivity is never a premise.
private def signedMatrix : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ :=
  fun _ i j => if i=j then (if i=0 then 1 else -1) else 0

example : MixedCode.evaluate repeated repeated_valid signedMatrix (fun (_ : Fin 1) _ => 1) (fun _ => 1) =
    ((components repeated).map
      (MixedCode.totalEvaluation signedMatrix (fun (_ : Fin 1) _ => 1) (fun _ => 1))).prod :=
  evaluate_components repeated repeated_valid _ _ _

private def cancellingLoop : MixedCode := ⟨1,[(0,0,0)],[]⟩
private theorem cancellingLoop_valid : cancellingLoop.Valid 1 1 := by
  simp [cancellingLoop,MixedCode.Valid]

example : cancellingLoop.evaluate cancellingLoop_valid signedMatrix
    (fun (_ : Fin 1) _ => 1) (fun _ => 1) = 0 := by
  have h := Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
    (assignmentWeight cancellingLoop signedMatrix (fun (_ : Fin 1) _ => 1) (fun _ => 1))
    (fun c : Fin 2 => if c=0 then (1:ℚ) else -1) (fun σ => by
      simp [assignmentWeight,cancellingLoop,MixedCode.binaryValue,signedMatrix,
        Equiv.funUnique,Equiv.piUnique])
  change (∑ σ : Fin 1 → Fin 2, assignmentWeight cancellingLoop signedMatrix
    (fun (_ : Fin 1) _ => 1) (fun _ => 1) σ) = 0
  rw [h]
  norm_num [Fin.sum_univ_two]

#print axioms partVertexEquiv
#print axioms componentColoringEquiv
#print axioms assignmentWeight_factorization
#print axioms evaluate_components
#print axioms componentReduction
