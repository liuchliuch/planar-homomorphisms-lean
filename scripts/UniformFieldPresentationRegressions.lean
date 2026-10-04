import PlanarHom.UniformFieldPresentationFamilies

open PlanarHom PlanarHom.Complexity PlanarHom.FieldCoordinateCertificates
open PlanarHom.UniformFieldPresentationHeights

-- Structure-height advice is derived from the exact presentation, not hypothesized.
example {K : Type} [Field K] [Algebra ℚ K] {d c : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (hc : d ≤ c) :
    Certificate.heightConstant (cleared basis) ≤
      2 ^ ((presentationExponentPolynomial c).eval (presentationBits basis+1)) :=
  heightConstant_le_pow_presentation basis hc

-- Even the total recovery bound now has no structure-height assumption.
example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {d c : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (hc : d ≤ c)
    (input : MaterializedLagrangeRecoveryMachines.Data K) :
    ((numberFieldEncoding basis).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
      (presentationOutputPolynomial c).eval
        (((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length+presentationBits basis) :=
  recovery_encoding_bound basis hc input

-- The source's actual FP presentation generator yields one bound across varying fields.
example {X : Type} (ex : BitEncoding X) (K : X → Type)
    [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
    (d : X → ℕ) (basis : ∀ x, Module.Basis (Fin (d x)) ℚ (K x))
    (c : ℕ) (hc : ∀ x, d x ≤ c)
    (hp : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ p : Polynomial ℕ, ∀ (x : X) (input : MaterializedLagrangeRecoveryMachines.Data (K x)),
      ((numberFieldEncoding (basis x)).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
        p.eval ((ex.encode x).length +
          ((MaterializedLagrangeRecoveryMachines.inputEncoding (basis x)).encode input).length) :=
  UniformFieldPresentationFamilies.exists_recovery_output_polynomial ex K d basis c hc hp
