import PlanarHom.UniformFieldPresentationHeights

/-! Uniform height budgets derived from actual FP presentations of varying number fields. -/
noncomputable section
namespace PlanarHom.UniformFieldPresentationFamilies
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds MachineComposition
open UniformFieldPresentationHeights UniformFieldHeights
variable {X : Type} (ex : BitEncoding X) (K : X → Type)
variable [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))

/-- Source effective presentations supply their own polynomial structure-height
budget. The polynomial follows from the actual presentation-output machine. -/
theorem exists_height_polynomial (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ p : Polynomial ℕ, ∀ x,
      Certificate.heightConstant (cleared (basis x)) ≤ 2 ^ (p.eval (ex.encode x).length) := by
  obtain ⟨computer⟩ := hpresentation
  let Q := outputLengthPolynomial computer
  let P := (presentationExponentPolynomial c).comp (Q+1)
  refine ⟨P, fun x => ?_⟩
  have hbits : presentationBits (basis x) ≤ Q.eval (ex.encode x).length := encoded_output_length_le computer x
  apply (heightConstant_le_pow_presentation (basis x) (hc x)).trans
  apply Nat.pow_le_pow_right (by omega)
  simpa only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one] using
    natPolynomial_monotone (presentationExponentPolynomial c) (Nat.add_le_add_right hbits 1)

/-- The same actual presentation witness bounds arbitrary dynamic field sums,
products, and coefficient prefixes in parameter bits plus literal value-list bits. -/
theorem exists_list_output_polynomial (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ p : Polynomial ℕ, ∀ (x : X) (xs : List (K x)) (i : ℕ),
      let N := (ex.encode x).length + ((numberFieldEncoding (basis x)).list.encode xs).length
      ((numberFieldEncoding (basis x)).encode xs.prod).length ≤ p.eval N ∧
      ((numberFieldEncoding (basis x)).encode xs.sum).length ≤ p.eval N ∧
      ((numberFieldEncoding (basis x)).list.encode (LagrangeCoefficientMachines.productCoefficients (xs.take i))).length ≤
        p.eval N := by
  obtain ⟨H,hH⟩ := exists_height_polynomial ex K dimension basis c hc hpresentation
  let P := (allHeightsPolynomial c).comp (Polynomial.X+H)
  refine ⟨P, fun x xs i => ?_⟩
  have hb := UniformFieldHeights.list_encoding_bounds (cleared (basis x)) (hc x) (hH x) xs i
  have hm : ((numberFieldEncoding (basis x)).list.encode xs).length + H.eval (ex.encode x).length ≤
      ((ex.encode x).length + ((numberFieldEncoding (basis x)).list.encode xs).length) +
        H.eval ((ex.encode x).length + ((numberFieldEncoding (basis x)).list.encode xs).length) := by
    have ht := natPolynomial_monotone H
      (show (ex.encode x).length ≤ (ex.encode x).length + ((numberFieldEncoding (basis x)).list.encode xs).length by omega)
    dsimp only at ht
    omega
  have hp := natPolynomial_monotone (allHeightsPolynomial c) hm
  simpa only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X] using
    And.intro (hb.1.trans hp) (And.intro (hb.2.1.trans hp) (hb.2.2.trans hp))

variable [∀ x, DecidableEq (K x)]

/-- No extra height advice for varying target fields: degree cap and the supplied
FP presentation alone produce one polynomial in parameter and recovery-input bits. -/
theorem exists_recovery_output_polynomial (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ p : Polynomial ℕ, ∀ (x : X) (input : MaterializedLagrangeRecoveryMachines.Data (K x)),
      ((numberFieldEncoding (basis x)).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
        p.eval ((ex.encode x).length +
          ((MaterializedLagrangeRecoveryMachines.inputEncoding (basis x)).encode input).length) := by
  obtain ⟨H,hH⟩ := exists_height_polynomial ex K dimension basis c hc hpresentation
  let P := (allHeightsPolynomial c).comp (Polynomial.X+H)
  refine ⟨P, fun x input => ?_⟩
  have hb := UniformFieldHeights.total_recovery_encoding_bound (cleared (basis x)) (hc x) (hH x) input
  apply hb.trans
  simp only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  apply natPolynomial_monotone
  have ht := natPolynomial_monotone H
    (show (ex.encode x).length ≤ (ex.encode x).length +
      ((MaterializedLagrangeRecoveryMachines.inputEncoding (basis x)).encode input).length by omega)
  dsimp only at ht
  omega

end PlanarHom.UniformFieldPresentationFamilies
