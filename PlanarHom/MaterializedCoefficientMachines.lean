import PlanarHom.MaterializedCoefficientHeights

/-! Actual linear-factor coefficient updates on arbitrary materialized node lists. -/
namespace PlanarHom.MaterializedCoefficientMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines MachineComposition
open LinearFactorCoefficientMachines LagrangeCoefficientMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The seed and original node list are physically present in the prepared word. -/
noncomputable def preparedEncoding : BitEncoding (List K) :=
  (((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list).retract
    (fun nodes => ([1], nodes)) Prod.snd (fun _ => rfl))

theorem fp_prepare : FP (numberFieldEncoding basis).list (preparedEncoding basis) id :=
  (((fp_const (numberFieldEncoding basis).list (numberFieldEncoding basis).list [1]).pair
    (fp_id (numberFieldEncoding basis).list))).transportOutput (fun _ => rfl)

theorem fp_coefficientStep : FP ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis))
    (numberFieldEncoding basis).list (fun p => mulLinear p.2 p.1) :=
  (((fp_snd (numberFieldEncoding basis).list (numberFieldEncoding basis)).pair
    (fp_fst (numberFieldEncoding basis).list (numberFieldEncoding basis)))).comp (fp_mulLinear basis)

/-- A single polynomial pays for every reachable prefix coefficient list from
literal input bits, including repeated, zero, and unrelated field nodes. -/
theorem exists_prefix_encoding_bound : ∃ p : Polynomial ℕ, ∀ (nodes : List K) (i : ℕ),
    ((numberFieldEncoding basis).list.encode (productCoefficients (nodes.take i))).length ≤
      p.eval ((numberFieldEncoding basis).list.encode nodes).length := by
  obtain ⟨p, hp⟩ := MaterializedCoefficientHeights.exists_polynomial_encoding_bound basis
  refine ⟨p, fun nodes i => hp _ _ ?_ ?_⟩
  · exact (by simp only [List.length_take]; exact Nat.min_le_right _ _ : (nodes.take i).length ≤ nodes.length).trans ((numberFieldEncoding basis).list_length_le nodes)
  · intro x hx
    exact MaterializedFieldHeights.element_length_le_list _ nodes (List.mem_of_mem_take hx)

/-- Total actual FP recovery of all ascending coefficients of ∏ (X - μ).
The proof-only Boolean expansion never appears in this machine: it runs the
existing linear-factor update once for each literal node. -/
theorem fp_productCoefficients : FP (numberFieldEncoding basis).list
    (numberFieldEncoding basis).list (productCoefficients : List K → List K) := by
  obtain ⟨p, hp⟩ := exists_prefix_encoding_bound basis
  obtain ⟨body⟩ := fp_coefficientStep basis
  have hsize (nodes : List K) (i : ℕ) (_hi : i ≤ nodes.length) :
      ((numberFieldEncoding basis).list.encode
        ((nodes.take i).foldl (fun cs μ => mulLinear μ cs) [1])).length ≤
      p.eval ((preparedEncoding basis).encode nodes).length := by
    apply (hp nodes i).trans
    apply natPolynomial_monotone
    change ((numberFieldEncoding basis).list.encode nodes).length ≤
      (((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list).encode ([1], nodes)).length
    simp only [BitEncoding.prod_length]
    omega
  have loop := ListFoldMachines.computerOn (preparedEncoding basis) (numberFieldEncoding basis)
    (numberFieldEncoding basis).list (fun cs μ => mulLinear μ cs) (fun _ => [1]) id
    (fun _ => rfl) body p hsize
  exact ((fp_prepare basis).comp ⟨loop⟩).congr (fun _ => rfl)

end PlanarHom.MaterializedCoefficientMachines
