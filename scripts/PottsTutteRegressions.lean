import PlanarHom.PottsTutteIdentity
import PlanarHom.PottsComponentCode

/-!
# Literal Potts/Tutte regressions

These tests retain loops, independently indexed parallel occurrences, and isolated
vertices. Empty and singleton color types require no nonzero-color hypothesis.
-/

open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.GraphComponentCode
noncomputable section
open Classical

namespace PottsTutteRegressions

private def emptyCode : MixedCode := ⟨0, [], []⟩
private def isolatedCode : MixedCode := ⟨3, [], []⟩
private def loopCode : MixedCode := ⟨1, [(0, 0, 0)], []⟩
private def parallelCode : MixedCode := ⟨2, [(0, 1, 0), (0, 1, 0)], []⟩
private def mixedCode : MixedCode :=
  ⟨3, [(0, 0, 0), (0, 1, 0), (0, 1, 0)], []⟩

private theorem empty_valid : emptyCode.Valid 1 0 := by
  simp [emptyCode, MixedCode.Valid]
private theorem isolated_valid : isolatedCode.Valid 1 0 := by
  simp [isolatedCode, MixedCode.Valid]
private theorem loop_valid : loopCode.Valid 1 0 := by
  simp [loopCode, MixedCode.Valid]
private theorem parallel_valid : parallelCode.Valid 1 0 := by
  simp [parallelCode, MixedCode.Valid]
private theorem mixed_valid : mixedCode.Valid 1 0 := by
  simp [mixedCode, MixedCode.Valid]

private abbrev emptyGraph := emptyCode.toMultiGraph empty_valid
private abbrev isolatedGraph := isolatedCode.toMultiGraph isolated_valid
private abbrev loopGraph := loopCode.toMultiGraph loop_valid
private abbrev parallelGraph := parallelCode.toMultiGraph parallel_valid
private abbrev mixedGraph := mixedCode.toMultiGraph mixed_valid

-- The executable component algorithm sees every original vertex, including
-- isolated vertex 2 in the mixed example.
example : parts emptyCode = [] := by decide
example : parts isolatedCode = [[2], [1], [0]] := by decide
example : parts loopCode = [[0]] := by decide
example : parts parallelCode = [[1, 0]] := by decide
example : parts mixedCode = [[0, 1], [2]] := by decide

private theorem empty_components : emptyGraph.componentCount Finset.univ = 0 := by
  rw [componentCount_eq_parts_length]
  decide
private theorem isolated_components : isolatedGraph.componentCount Finset.univ = 3 := by
  rw [componentCount_eq_parts_length]
  decide
private theorem loop_components : loopGraph.componentCount Finset.univ = 1 := by
  rw [componentCount_eq_parts_length]
  decide
private theorem parallel_components : parallelGraph.componentCount Finset.univ = 1 := by
  rw [componentCount_eq_parts_length]
  decide
private theorem mixed_components : mixedGraph.componentCount Finset.univ = 2 := by
  rw [componentCount_eq_parts_length]
  decide

private abbrev potts (q : ℕ) : Matrix (Fin q) (Fin q) ℤ :=
  1 + Matrix.of (fun _ _ => 1)

-- A singleton color type contributes one factor of two per edge occurrence.
private theorem loop_one : loopGraph.partition (potts 1) (fun _ => 1) = 2 := by
  norm_num [MultiGraph.partition, MultiGraph.assignmentWeight, potts,
    loopGraph, loopCode, MixedCode.toMultiGraph, Matrix.one_apply]

private theorem parallel_one : parallelGraph.partition (potts 1) (fun _ => 1) = 4 := by
  norm_num [MultiGraph.partition, MultiGraph.assignmentWeight, potts,
    parallelGraph, parallelCode, MixedCode.toMultiGraph, Matrix.one_apply]

private theorem mixed_one : mixedGraph.partition (potts 1) (fun _ => 1) = 8 := by
  norm_num [MultiGraph.partition, MultiGraph.assignmentWeight, potts,
    mixedGraph, mixedCode, MixedCode.toMultiGraph, Matrix.one_apply]

section ClassicalEnumeration

local instance (priority := 10000) classicalRegressionDecEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

-- Expanding assignments through a proved equivalence keeps these computations
-- in the kernel, including all off-diagonal interactions at q = 2.
private theorem sum_assignments_succ (n q : ℕ)
    (f : (Fin (n + 1) → Fin q) → ℤ) :
    (∑ σ, f σ) = ∑ c : Fin q, ∑ σ : Fin n → Fin q, f (Fin.cons c σ) := by
  calc
    _ = ∑ p : Fin q × (Fin n → Fin q), f (Fin.cons p.1 p.2) :=
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin q)) f).symm
    _ = _ := Fintype.sum_prod_type _

private theorem parallel_two : parallelGraph.partition (potts 2) (fun _ => 1) = 10 := by
  dsimp only [parallelGraph, parallelCode, MultiGraph.partition,
    MultiGraph.assignmentWeight, MixedCode.toMultiGraph, List.length_cons, List.length_nil]
  rw [sum_assignments_succ 1 2]
  simp_rw [sum_assignments_succ 0 2]
  norm_num [sum_assignments_succ, MultiGraph.partition, MultiGraph.assignmentWeight, potts,
    parallelGraph, parallelCode, MixedCode.toMultiGraph, Matrix.one_apply,
    Fin.sum_univ_two, Fin.prod_univ_succ, List.length_cons, List.length_nil]

private theorem mixed_two : mixedGraph.partition (potts 2) (fun _ => 1) = 40 := by
  dsimp only [mixedGraph, mixedCode, MultiGraph.partition,
    MultiGraph.assignmentWeight, MixedCode.toMultiGraph, List.length_cons, List.length_nil]
  rw [sum_assignments_succ 2 2]
  simp_rw [sum_assignments_succ 1 2, sum_assignments_succ 0 2]
  norm_num [sum_assignments_succ, MultiGraph.partition, MultiGraph.assignmentWeight, potts,
    mixedGraph, mixedCode, MixedCode.toMultiGraph, Matrix.one_apply,
    Fin.sum_univ_two, Fin.prod_univ_succ, List.length_cons, List.length_nil]

end ClassicalEnumeration

-- The nonempty input has no assignments from its vertices to zero colors.
private theorem mixed_zero : mixedGraph.partition (potts 0) (fun _ => 1) = 0 := by
  simp [MultiGraph.partition, mixedGraph, mixedCode]

-- The empty input still has exactly one empty assignment, also at q = 0.
private theorem empty_zero : emptyGraph.partition (potts 0) (fun _ => 1) = 1 := by
  simp [MultiGraph.partition, MultiGraph.assignmentWeight, emptyGraph, emptyCode]

-- Three isolated vertices have three independent color choices.
private theorem isolated_two : isolatedGraph.partition (potts 2) (fun _ => 1) = 8 := by
  haveI : IsEmpty (Fin isolatedCode.edges.length) := by
    change IsEmpty (Fin 0)
    infer_instance
  rw [MultiGraph.partition_edgeless]
  norm_num [isolatedGraph, isolatedCode]

-- The same theorem specializes directly to q = 0, without cancellation or
-- division by the component factor.
example : mixedGraph.partition (potts 0) (fun _ => 1) =
    (0 : ℤ) ^ 2 * mixedGraph.rankSubsetTutte 1 2 := by
  simpa only [potts, mixed_components, Nat.cast_zero, zero_add] using
    mixedGraph.potts_tutte_fin (R := ℤ) 0

example : emptyGraph.partition (potts 0) (fun _ => 1) =
    (0 : ℤ) ^ 0 * emptyGraph.rankSubsetTutte 1 2 := by
  simpa only [potts, empty_components, Nat.cast_zero, zero_add] using
    emptyGraph.potts_tutte_fin (R := ℤ) 0

example : mixedGraph.partition (potts 1) (fun _ => 1) =
    (1 : ℤ) ^ 2 * mixedGraph.rankSubsetTutte 2 2 := by
  simpa only [potts, mixed_components, Nat.cast_one, show (1 : ℤ) + 1 = 2 from rfl] using
    mixedGraph.potts_tutte_fin (R := ℤ) 1

-- Exact evaluations of the independent rank-subset polynomial follow from
-- the identity and the literal partition calculations above.
example : loopGraph.rankSubsetTutte (2 : ℤ) 2 = 2 := by
  have h := loopGraph.potts_tutte_fin (R := ℤ) 1
  simpa [← loop_one, potts] using h.symm

example : parallelGraph.rankSubsetTutte (2 : ℤ) 2 = 4 := by
  have h := parallelGraph.potts_tutte_fin (R := ℤ) 1
  simpa [← parallel_one, potts] using h.symm

example : mixedGraph.rankSubsetTutte (2 : ℤ) 2 = 8 := by
  have h := mixedGraph.potts_tutte_fin (R := ℤ) 1
  simpa [← mixed_one, potts] using h.symm

example : emptyGraph.rankSubsetTutte (1 : ℤ) 2 = 1 := by
  have h := emptyGraph.potts_tutte_fin (R := ℤ) 0
  simpa only [empty_components, Nat.cast_zero, zero_add, pow_zero, one_mul,
    potts, empty_zero] using h.symm

private theorem parallel_tutte_three_two :
    parallelGraph.rankSubsetTutte (3 : ℤ) 2 = 5 := by
  have h := parallelGraph.potts_tutte_fin (R := ℤ) 2
  rw [parallel_two, parallel_components] at h
  norm_num at h
  omega

private theorem mixed_tutte_three_two :
    mixedGraph.rankSubsetTutte (3 : ℤ) 2 = 10 := by
  have h := mixedGraph.potts_tutte_fin (R := ℤ) 2
  rw [mixed_two, mixed_components] at h
  norm_num at h
  omega

#print axioms MultiGraph.potts_tutte
#print axioms MultiGraph.potts_tutte_fin
#print axioms componentCount_eq_parts_length
#print axioms mixed_components
#print axioms mixed_zero
#print axioms loop_one
#print axioms parallel_one
#print axioms mixed_one
#print axioms parallel_two
#print axioms mixed_two
#print axioms parallel_tutte_three_two
#print axioms mixed_tutte_three_two
#print axioms empty_zero
#print axioms isolated_two

end PottsTutteRegressions
