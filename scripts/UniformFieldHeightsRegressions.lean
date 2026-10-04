import PlanarHom.UniformFieldRecoveryHeights

open PlanarHom PlanarHom.Complexity PlanarHom.IntegerCoordinateBounds
open PlanarHom.FieldCoordinateCertificates PlanarHom.UniformFieldHeights

-- The polynomial is chosen before the field, dimension, basis, and structure data.
example (c : ℕ) : ∃ p : Polynomial ℕ,
    ∀ (K : Type) [Field K] [Algebra ℚ K] [DecidableEq K] (d : ℕ)
      (basis : Module.Basis (Fin d) ℚ K)
      (data : ClearedCoordinates basis (fun k : Fin d => basis k)) (H : ℕ),
      d ≤ c → Certificate.heightConstant data ≤ 2^H →
      ∀ input : MaterializedLagrangeRecoveryMachines.Data K,
        ((numberFieldEncoding basis).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
          p.eval (((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length+H) := by
  refine ⟨allHeightsPolynomial c, ?_⟩
  intro K field algebra eq d basis data H hd hdata input
  exact total_recovery_encoding_bound data hd hdata input

-- Every reachable coefficient prefix uses the same bound on the original input.
example {K : Type} [Field K] [Algebra ℚ K] {d c H : ℕ}
    (basis : Module.Basis (Fin d) ℚ K)
    (data : ClearedCoordinates basis (fun k : Fin d => basis k))
    (hd : d ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (xs : List K) (i : ℕ) :
    ((numberFieldEncoding basis).list.encode (LagrangeCoefficientMachines.productCoefficients (xs.take i))).length ≤
      (allHeightsPolynomial c).eval (((numberFieldEncoding basis).list.encode xs).length+H) :=
  (list_encoding_bounds data hd hdata xs i).2.2

-- Total inversion does not acquire a nonzero-input premise in the uniform bound.
example {K : Type} [Field K] [Algebra ℚ K] {d c H N : ℕ}
    (basis : Module.Basis (Fin d) ℚ K)
    (data : ClearedCoordinates basis (fun k : Fin d => basis k))
    (hd : d ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (x : K) (hx : ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).encode x⁻¹).length ≤ (inversePolynomial c).eval (N+H) :=
  (inverse_neg_encoding_bound data hd hdata x N hx).1
