import PlanarHom.PolynomialIntegerRootCandidateMachines

open PlanarHom Complexity Polynomial
open PolynomialIntegerRootCandidates PolynomialIntegerRootCandidateMachines
open DiscreteSignPartitionMachines

-- A repeated root is found even though the polynomial does not change sign.
example : 2 ∈ candidates 2 ((X-C 2 : ℚ[X])^2) 0 10 := by
  apply root_mem_candidates
  · compute_degree
  · exact pow_ne_zero _ (X_sub_C_ne_zero _)
  · omega
  · omega
  · norm_num

-- The half-open interval includes its left endpoint and excludes the right.
example : 0 ∈ candidates 1 (X : ℚ[X]) 0 1 := by
  apply root_mem_candidates <;> simp

example : 8 ∈ candidates 2 ((X-C 3 : ℚ[X])*(X-C 8)) 0 9 := by
  apply root_mem_candidates
  · compute_degree
  · exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  · omega
  · omega
  · norm_num

example (p : ℚ[X]) (l h : ℕ) : candidates 0 p l h = [] := by
  simp [candidates, PolynomialDiscretePartition.partition]

example (p : ℚ[X]) (l h : ℕ) : (candidates 2 p l h).length ≤ 18 := by
  simpa using candidates_length 2 p l h

-- Concrete family interface has an actual FP conclusion and no search oracle.
example (p : ℚ[X]) (hp : p.natDegree ≤ 3) :
    FP (BitEncoding.nat.prod intervalEncoding) BitEncoding.nat.list
      (fun a => candidates 3 p a.2.1 a.2.2) :=
  fp_candidates BitEncoding.nat (fun _ => p) 3 (fun _ => hp)
    (fun k => fp_const BitEncoding.nat BitEncoding.rat (p.coeff k))
