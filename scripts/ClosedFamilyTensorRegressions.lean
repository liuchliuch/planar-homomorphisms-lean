import PlanarHom.ClosedFamilyTensor

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
open PlanarHom PlanarHom.Boolean PlanarHom.CubeTensorExponential

-- The empty product is the genuine singleton matrix, including arbitrary local labels.
example (F : Fin 0 → Matrix Bool Bool ℝ) :
    CubeTensorExponential.tensor F = (1 : Matrix (Cube 0) (Cube 0) ℝ) := by
  ext z w
  have h : z = w := Subsingleton.elim _ _
  subst w
  simp [CubeTensorExponential.tensor]

-- A disconnected PD target has zero off-diagonal canonical factors, not strictly
-- positive ones. This guards the disconnected-target scope of Proposition 4.8.
example (r : Fin 2) : canonicalFactor (1 : Matrix (Cube 2) (Cube 2) ℝ) r =
    (1 : Matrix Bool Bool ℝ) := by
  have hz : (zeroColor : Cube 2) ≠ oneCoordinate r true := by
    intro h
    have hh := congrFun h r
    simp [zeroColor, oneCoordinate] at hh
  ext a b
  cases a <;> cases b <;> simp [canonicalFactor, hz]

-- The three differently labelled edges retain their ordered H*K*H semantics.
example : TwoTerminal.coloredSignature TwoTerminal.threeEdgePath
    (TwoTerminal.seriesMatrices
      (fun a b : Bool => if a then (if b then (5 : ℝ) else 2) else (if b then 2 else 1))
      (fun a b : Bool => if a then (if b then (3 : ℝ) else 1) else (if b then 1 else 2)))
    (fun _ => 1) false false = 18 := by
  rw [TwoTerminal.coloredSignature_threeEdgePath]
  norm_num [Matrix.mul_apply, Fintype.sum_bool]

-- One chart is fixed outside the target quantifier. Replacing a maximum by its
-- positive-log representative cannot silently choose a different chart for N.
example {q d : ℕ} (A : Set (Matrix (Fin q) (Fin q) ℝ))
    (hA : ClosedMatrixFamily.AlgebraicSourceClosed A)
    (htransfer : ClosedMatrixFamily.EffectiveSpectralClosed A)
    (hgadget : ClosedMatrixFamily.MixedPlanarGadgetClosed A)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : ClosedMatrixFamily.Admissible A M)
    (hmax : ClosedMatrixFamily.IsMaximum A M)
    (e : LogarithmicSupport.logSupport M ≃g cubeGraph d) :
    ∀ N : Matrix (Fin q) (Fin q) ℝ, N ∈ A → N.PosDef → (∀ i j, 0 ≤ N i j) →
      ∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
        ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r) := by
  intro N hN hpd hnn
  exact (ClosedMatrixFamily.proposition48_fixed_maximum
    A hA htransfer hgadget M hM hmax e N hN hpd hnn).1

-- Source-facing type audit: the only target premises are membership, PD and nonnegativity.
#check ClosedMatrixFamily.proposition48
#check ClosedMatrixFamily.proposition48_fixed_maximum
#print axioms ClosedMatrixFamily.proposition48
#print axioms ClosedMatrixFamily.proposition48_fixed_maximum
#print axioms ClosedMatrixFamily.rationalSquareSandwichEdgeBound
#print axioms ClosedMatrixFamily.rationalSandwichEdgeBound
#print axioms ClosedMatrixFamily.rationalSandwichSchurEdgeBound
#print axioms ClosedMatrixFamily.maximum_reindex
