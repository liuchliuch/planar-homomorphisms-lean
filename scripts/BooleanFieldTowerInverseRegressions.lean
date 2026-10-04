import PlanarHom.BooleanFieldTowerInverseMachines

open PlanarHom.BooleanFieldTower PlanarHom.BooleanFieldTowerAlgebra
open PlanarHom.BooleanFieldTowerInverse PlanarHom.BooleanFieldTowerReconstruction
open PlanarHom.BooleanFieldTowerEvaluation

-- A square radicand gives a genuine zero divisor: no tower field instance is used.
example : mul (fun _=>(1 : ℚ)) 1 (1,1) (1,-1)=zero 1 := by
  norm_num [mul,add,embed,zero]
example : (1,1)≠(zero 1 : Tower ℚ 1) := by
  simp [zero]
example : (1,-1)≠(zero 1 : Tower ℚ 1) := by
  simp [zero]

-- Recursive conjugation still inverts every norm-certified unit in that algebra.
example : inverse (fun _=>(1 : ℚ)) 1 (2,1)=(2/3,-1/3) := by
  norm_num [inverse,mul,sub,add,neg,embed,zero]
example : norm (fun _=>(1 : ℚ)) 2 ((3,1),(1,0))=45 := by
  norm_num [norm,mul,sub,add,neg,embed,zero]
example : mul (fun _=>(1 : ℚ)) 2 ((3,1),(1,0))
    (inverse (fun _=>(1 : ℚ)) 2 ((3,1),(1,0)))=embed 2 1 := by
  apply mul_inverse
  norm_num [norm,mul,sub,add,neg,embed,zero]

-- One real branch is not injective for square radicands.
example : eval (Rat.castHom ℝ) (fun _=>1) 1 (1,-1) (fun _=>false)=0 := by
  norm_num [eval]
-- All sign branches remain injective, even with both radicals equal to one.
example : Function.Injective (fun p : Tower ℚ 2=>fun σ=>
    eval (Rat.castHom ℝ) (fun _=>1) 2 p σ) := by
  apply allSign_injective (Rat.castHom ℝ) (Rat.castHom ℝ).injective
  intro i hi
  norm_num

-- Invariance forces every nonconstant coefficient to vanish; the common value
-- is exactly the base field constant coefficient.
example (p : Tower ℚ 2) (a : ℝ)
    (h : ∀σ,eval (Rat.castHom ℝ) (fun _=>1) 2 p σ=a) :
    p=embed 2 (constantCoeff 2 p) ∧ ((constantCoeff 2 p : ℚ) : ℝ)=a := by
  exact reconstruction (Rat.castHom ℝ) (Rat.castHom ℝ).injective (fun _=>1) 2
    (by intro i hi; norm_num) p a h
example (p : Tower ℚ 2) (a : ℝ)
    (h : ∀σ,eval (Rat.castHom ℝ) (fun _=>1) 2 p σ=a) :
    coefficient 2 p (fun _=>true)=0 := by
  exact nonconstant_coefficients_vanish (Rat.castHom ℝ) (Rat.castHom ℝ).injective
    (fun _=>1) 2 (by intro i hi; norm_num) p a h (fun _=>true) ⟨0,rfl⟩

-- The total inverse has an actual FP implementation with no radical oracle,
-- sample-dependent field presentation, machine premise, or height premise.
example {K : Type} [Field K] [Algebra ℚ K] {d n : ℕ}
    (b : Module.Basis (Fin d) ℚ K) (D : ℕ→K) :
    PlanarHom.Complexity.FP (PlanarHom.BooleanFieldTowerMachines.encoding b n)
      (PlanarHom.BooleanFieldTowerMachines.encoding b n) (inverse D n) := by
  exact PlanarHom.BooleanFieldTowerInverseMachines.fp_inverse b _ (fun _=>D)
    (fun i=>PlanarHom.Complexity.fp_const _ _ (D i)) n id
    (PlanarHom.Complexity.fp_id _)
