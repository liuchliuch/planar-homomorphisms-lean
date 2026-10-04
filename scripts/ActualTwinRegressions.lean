import PlanarHom.ActualTwinRowFacts
import PlanarHom.ActualTwinZeroMatrix
import PlanarHom.ActualTwinRemoval

/-! Signed actual twins, zero interactions, and exact class aggregation. -/

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode

namespace PlanarHom.ActualTwinRegressions

def signedMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

theorem signedMatrix_symmetric : ∀ i j, signedMatrix i j = signedMatrix j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem signedMatrix_rows_distinct : signedMatrix 0 ≠ signedMatrix 1 := by
  intro h
  have he := congrFun h 0
  norm_num [signedMatrix] at he

abbrev SignedClasses := Quotient (Twins.rowSetoid signedMatrix)

def signedClass0 : SignedClasses := Quotient.mk _ (0 : Fin 2)
def signedClass1 : SignedClasses := Quotient.mk _ (1 : Fin 2)

theorem signedClasses_distinct : signedClass0 ≠ signedClass1 := by
  intro h
  apply signedMatrix_rows_distinct
  funext k
  exact (Quotient.exact h) k

def signedQuotient : Matrix SignedClasses SignedClasses ℝ :=
  Twins.quotientMatrix signedMatrix signedMatrix_symmetric

theorem signedQuotient_rows_opposite :
    signedQuotient signedClass0 = (-1 : ℝ) • signedQuotient signedClass1 := by
  funext x
  induction x using Quotient.inductionOn with
  | h k =>
    change signedMatrix 0 k = (-1 : ℝ) * signedMatrix 1 k
    fin_cases k <;> norm_num [signedMatrix]

/-- Equality of actual rows does not identify opposite signed rows. Hence
the actual quotient alone does not guarantee nonproportionality. -/
theorem signedQuotient_not_rows_nonproportional :
    ¬ (∀ i j : SignedClasses, i ≠ j → ∀ c : ℝ,
      signedQuotient i ≠ c • signedQuotient j) := by
  intro h
  exact h signedClass0 signedClass1 signedClasses_distinct (-1)
    signedQuotient_rows_opposite

private def weights : Fin 2 → ℚ := ![2, 3]
private def emptyInput : MixedCode := ⟨0, [], []⟩
private def isolatedInput : MixedCode := ⟨3, [], []⟩
private def loopInput : MixedCode := ⟨1, [(0, 0, 0)], []⟩

private theorem emptyInput_valid : emptyInput.Valid 1 0 := by simp [emptyInput, Valid]
private theorem isolatedInput_valid : isolatedInput.Valid 1 0 := by simp [isolatedInput, Valid]
private theorem loopInput_valid : loopInput.Valid 1 0 := by simp [loopInput, Valid]

-- Three isolated vertices contribute one full weight sum each: (2+3)^3.
example : totalEvaluation (fun _ : Fin 1 => (0 : Matrix (Fin 2) (Fin 2) ℚ))
    (fun u : Fin 0 => Fin.elim0 u) weights isolatedInput = 125 := by
  rw [totalEvaluation_zeroMatrix isolatedInput isolatedInput_valid]
  norm_num [isolatedInput, weights, Fin.sum_univ_two]

-- A loop is an edge and therefore annihilates the zero-matrix value.
example : totalEvaluation (fun _ : Fin 1 => (0 : Matrix (Fin 2) (Fin 2) ℚ))
    (fun u : Fin 0 => Fin.elim0 u) weights loopInput = 0 := by
  rw [totalEvaluation_zeroMatrix loopInput loopInput_valid]
  simp [loopInput]

-- The empty input retains the empty assignment, even with no colors.
example : totalEvaluation (fun _ : Fin 1 => (0 : Matrix Empty Empty ℚ))
    (fun u : Fin 0 => Fin.elim0 u) (fun i : Empty => i.elim) emptyInput = 1 := by
  exact totalEvaluation_zeroMatrix_of_vertices_zero emptyInput emptyInput_valid rfl _

example : MultiGraph.isolatedVertex.partition (0 : Matrix (Fin 2) (Fin 2) ℚ)
    weights = 5 := by
  rw [MultiGraph.partition_isolatedVertex]
  norm_num [weights, Fin.sum_univ_two]

example : MultiGraph.emptyGraph.partition (0 : Matrix Empty Empty ℚ)
    (fun i : Empty => i.elim) = 1 := MultiGraph.partition_emptyGraph _ _

-- Deleting zero actual rows leaves an empty target color set for A=0.
example : ActualTwins.reducedCount (0 : Matrix (Fin 2) (Fin 2) ℚ)
    (fun _ _ => rfl) = 0 :=
  ActualTwins.reducedCount_eq_zero _ _ rfl

-- The resulting ordinary target has no assignments on an isolated vertex.
example : MultiGraph.isolatedVertex.partition
    (ActualTwins.reducedMatrix (0 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ _ => rfl))
    (fun _ => 1) = 0 := by
  have hn := ActualTwins.reducedCount_eq_zero (0 : Matrix (Fin 2) (Fin 2) ℚ)
    (fun _ _ => rfl) rfl
  letI : IsEmpty (Fin (ActualTwins.reducedCount (0 : Matrix (Fin 2) (Fin 2) ℚ)
      (fun _ _ => rfl))) := ⟨fun i => Nat.not_lt_zero i.val (hn ▸ i.isLt)⟩
  simp

-- Its empty input still has the unique empty assignment.
example : MultiGraph.emptyGraph.partition
    (ActualTwins.reducedMatrix (0 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ _ => rfl))
    (fun _ => 1) = 1 := MultiGraph.partition_emptyGraph _ _

private def identicalRows : Matrix (Fin 2) (Fin 2) ℚ := fun _ _ => 1
private theorem identicalRows_symmetric : ∀ i j, identicalRows i j = identicalRows j i :=
  fun _ _ => rfl

-- Actual twins merge their unequal positive weights by addition.
theorem identicalRows_class_weight :
    Twins.quotientWeight identicalRows weights (Quotient.mk _ (0 : Fin 2)) = 5 := by
  have hclass : ∀ i : Fin 2, Quotient.mk (Twins.rowSetoid identicalRows) i =
      Quotient.mk (Twins.rowSetoid identicalRows) (0 : Fin 2) := by
    intro i
    exact Quotient.sound (fun _ => rfl)
  unfold Twins.quotientWeight
  calc
    _ = ∑ i : Fin 2, weights i :=
      Fintype.sum_equiv (Equiv.subtypeUnivEquiv hclass)
        (fun i => weights i.val) weights (fun _ => rfl)
    _ = 5 := by norm_num [weights, Fin.sum_univ_two]

example {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E) :
    G.partition identicalRows weights =
      G.partition (Twins.quotientMatrix identicalRows identicalRows_symmetric)
        (Twins.quotientWeight identicalRows weights) :=
  Twins.partition_canonicalQuotient G identicalRows weights identicalRows_symmetric

#print axioms MultiGraph.partition_zeroMatrix
#print axioms evaluate_zeroMatrix
#print axioms totalEvaluation_zeroMatrix
#print axioms evaluate_zeroMatrix_of_vertices_zero
#print axioms totalEvaluation_zeroMatrix_of_vertices_zero
#print axioms signedClasses_distinct
#print axioms signedQuotient_rows_opposite
#print axioms signedQuotient_not_rows_nonproportional
#print axioms identicalRows_class_weight
#print axioms ActualTwins.reducedCount_eq_zero

end PlanarHom.ActualTwinRegressions
