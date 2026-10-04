import PlanarHom.BooleanFieldNormSamples

open PlanarHom.BooleanFieldTower PlanarHom.BooleanFieldCollision
open PlanarHom.BooleanFieldCollisionMachines

-- The fixed-field evaluator computes the literal nonzero norm in Q.
example : collision (fun _ : Fin 1 => (5/4 : ℚ)) (fun _ => 3/4) (fun _ => 1/2)
    (1/2) (fun _ => 1) (fun _ => 0) (fun _ => 1) = -5/2 := by
  norm_num [collision,spectral,product,power,mul,sub,add,neg,embed,zero,linear,
    PlanarHom.BooleanFieldTower.norm,radicands,extend,Fin.lastCases]

-- Oversized binary count inputs are clipped to their explicit unary cap.
example : evaluate (fun _ : Fin 1 => (5/4 : ℚ)) (fun _ => 3/4) (fun _ => 1/2)
    (1,(1/2,(fun _ => 1,(fun _ => 7,fun _ => 9)))) = 0 := by
  norm_num [evaluate,totals,leftCounts,rightCounts,collision,spectral,product,power,mul,
    sub,add,neg,embed,zero,linear,PlanarHom.BooleanFieldTower.norm,radicands,extend,Fin.lastCases]

-- The bridge identifies this exact computation with the existing real
-- polynomial and does not ask for root values or an algebraic overfield.
example {b : ℕ} (c a w : Fin b → ℚ) (q : ℚ) (n k l : Fin b → ℕ) :
    ((collision c a w q n k l : ℚ) : ℝ) =
      (PlanarHom.BooleanExceptionalPolynomial.collisionPolynomial
        (fun i => (c i : ℝ)) (fun i => (a i : ℝ)) (fun i => (w i : ℝ)) n k l).eval (q : ℝ) :=
  collision_eval (Rat.castHom ℝ) c a w q n k l

-- The actual FP endpoint has no machine, oracle, or height-bound premise.
example {K : Type} [Field K] [Algebra ℚ K] {dimension b : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (c a w : Fin b → K) :
    PlanarHom.Complexity.FP (inputEncoding b) (PlanarHom.Complexity.numberFieldEncoding basis)
      (evaluate c a w) := fp_evaluate basis c a w
