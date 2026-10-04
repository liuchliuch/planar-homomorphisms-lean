import PlanarHom.QuadraticBinomialPowerMachines

open PlanarHom PlanarHom.QuadraticBinomialPowerMachines
open PlanarHom.Complexity PlanarHom.ArithmeticCircuitPrimitives

example : branchPower (0, ((3, 5) : ℚ × ℚ)) = (1, 0) := by
  norm_num [branchPower, component, term]

example : branchPower (5, ((3, 5) : ℚ × ℚ)) = (1968, 880) := by
  norm_num [branchPower, component, term, List.range_succ, Nat.choose]

example {K : Type} [Field K] (c D : K) : branchPower (2,(c,D)) = (c^2+D, 2*c) := by
  rw [branchPower_eq_quadraticPower]
  apply Prod.ext <;> simp [pow_two]
  ring

example {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ K) :
    FP (inputEncoding b) ((numberFieldEncoding b).prod (numberFieldEncoding b))
      branchPower := fp_branchPower b

example {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ K) :
    FP (BitEncoding.unaryNat.prod BitEncoding.nat) (numberFieldEncoding b)
      (fun p : ℕ × ℕ => (p.1.choose p.2 : K)) := fp_choose b
