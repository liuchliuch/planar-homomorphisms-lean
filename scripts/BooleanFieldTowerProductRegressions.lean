import PlanarHom.BooleanFieldTowerProductMachines

noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.BooleanFieldTower
open PlanarHom.BooleanFieldTowerMachines PlanarHom.BooleanFieldTowerProductMachines

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (basis : Module.Basis (Fin d) ℚ K)

example (b : ℕ) :
    FP ((numberFieldEncoding basis).list.prod
      ((encoding basis b).prod (encoding basis b).list)) (encoding basis b)
      (fun p : List K × (Tower K b × List (Tower K b)) =>
        p.2.2.foldl (mul (fun i => p.1[i]?.getD 0) b) p.2.1) :=
  BooleanFieldTowerProductMachines.fp_product basis b

example (b : ℕ) : ∃ p : Polynomial ℕ,
    ∀ (ds : List K) (a : Tower K b) (xs : List (Tower K b)) (i : ℕ),
      ((encoding basis b).encode ((xs.take i).foldl (mul (radicands ds) b) a)).length ≤
        p.eval ((inputEncoding basis b).encode (ds,(a,xs))).length :=
  exists_polynomial_prefix_encoding_bound basis b

-- Zero radicands are admitted: the represented algebra can have nilpotents.
example : mul (fun _ => (0 : ℚ)) 1 (0,1) (0,1) = (0,0) := by
  norm_num [mul,embed,add]

-- Square radicands are also admitted: the represented algebra can have zero divisors.
example : mul (fun _ => (1 : ℚ)) 1 (1,1) (1,-1) = (0,0) := by
  norm_num [mul,embed,add]

example (a : K) : product 0 ([],(a,[])) = a := rfl

example (a x y : K) : product 0 ([],(a,[x,y])) = (a*x)*y := rfl

#print axioms PlanarHom.SharedLinearCertificates.fold_encoding_bound
#print axioms PlanarHom.LinearFoldMachines.fp_fold
#print axioms PlanarHom.BooleanFieldTowerLinearization.coord_mul
#print axioms PlanarHom.BooleanFieldTowerProductMachines.fp_product
#print axioms PlanarHom.BooleanFieldTowerProductMachines.exists_polynomial_prefix_encoding_bound
#print axioms PlanarHom.BooleanFieldTowerProductMachines.product_eq
