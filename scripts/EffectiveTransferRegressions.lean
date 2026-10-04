import PlanarHom.UniformFixedFieldTransfer

open PlanarHom PlanarHom.Complexity PlanarHom.ExponentProductTables
open PlanarHom.ExponentProductSemantics PlanarHom.EffectiveProductTransfer
open PlanarHom.MaterializedLagrangeRecoveryMachines PlanarHom.LagrangeCoefficientMachines
open PlanarHom.LinearFactorCoefficientMachines

-- Empty products require no source compatibility restriction, even for signed/zero targets.
example : CompatibleAt (fun _ : Fin 2 => (0 : ℚ)) (fun i => if i=0 then -3 else 0) 0 :=
  compatibleAt_zero _ _

-- At a positive marked length, an actual source collision with unequal targets is rejected.
example : ¬CompatibleAt (fun _ : Fin 2 => (1 : ℚ)) (fun i => if i=0 then -3 else 0) 1 := by
  intro h
  have he := h [1,0] (by simp [ExponentVectors.mem_weak]) [0,1]
    (by simp [ExponentVectors.mem_weak]) (by norm_num [value, Fin.prod_univ_two])
    (by norm_num [value, Fin.prod_univ_two])
  norm_num [value, Fin.prod_univ_two] at he

-- Exact recovery admits a signed target and a new zero target at the same time.
example : recover (([(2, -3), (3, 0)], [5, 13]) : Data ℚ) = -3 := by
  norm_num [recover, rowTerm, otherNodes, productCoefficients, mulLinear, go,
    MaterializedFieldListMachines.shiftedDenominator]

-- Reversing an input edge preserves the actual upper-triangular entry identity.
example : SymmetricProductIdentities.orient ((1 : Fin 2),0) =
    SymmetricProductIdentities.orient ((0 : Fin 2),1) := by
  decide

-- Both source sample bounds include one candidate at marked length zero.
example : (polynomialCandidateCount 2 3).eval 0 = 1 := by norm_num
example : (spectralCandidateCount 2 2).eval 0 = 2 := by norm_num

-- The exact spectral stars-and-bars dimension is retained before polynomial relaxation.
example : (3 + 2 - 1).choose 2 - 1 = 5 := by decide
example : Fintype.card (Sym (Fin 3) 2) = 6 := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  decide

#print axioms EffectiveProductTransfer.polynomial_reduction
#print axioms EffectiveProductTransfer.spectral_reduction
#print axioms EffectiveProductTransfer.polynomial_parameter_reduction
#print axioms EffectiveProductTransfer.spectral_parameter_reduction
