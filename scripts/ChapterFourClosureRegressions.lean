import PlanarHom.ClosedFamilyLocalGeometry
import PlanarHom.DistanceKernelRealAvailability

open PlanarHom PlanarHom.ClosedMatrixFamily PlanarHom.LogarithmicSupport

private def algebraicFamily : Set (Matrix (Fin 1) (Fin 1) ℝ) :=
  {H | H.IsHermitian ∧ ∀ i j, IsAlgebraic ℚ (H i j)}

private theorem singletonAlgebraicClosure : AlgebraicSourceClosed algebraicFamily where
  symmetric := fun _ h => h.1
  algebraic := fun _ h => h.2
  spectral := by
    intro H hH hpd hAlg r
    exact ⟨cfc_predicate _ _, AlgebraicSpectralData.isAlgebraic_rationalPower_entry H hpd hAlg r⟩
  parallel := by
    intro H hH hsH K hK hsK
    refine ⟨?_, fun i j => (hH.2 i j).mul (hK.2 i j)⟩
    apply Matrix.IsHermitian.ext
    intro i j
    simpa using congrArg₂ (fun x y : ℝ => x * y) (hsH.apply i j) (hsK.apply i j)

private theorem unitAdmissible : Admissible algebraicFamily (1 : Matrix (Fin 1) (Fin 1) ℝ) where
  mem := ⟨Matrix.isHermitian_one, by intro i j; have h : i=j := Subsingleton.elim _ _; subst j; simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))⟩
  nonneg := by
    intro i j
    change (0 : ℝ) ≤ (1 : Matrix (Fin 1) (Fin 1) ℝ) i j
    rw [Subsingleton.elim i j, Matrix.one_apply_eq]
    norm_num
  posDef := Matrix.PosDef.one
  connected := by
    constructor
    intro i j
    have h : i=j := Subsingleton.elim _ _
    subst j
    exact SimpleGraph.Reachable.refl _

-- The one-color boundary has a genuine nonempty maximum class, with no required log edges.
example : ∃ M, Admissible algebraicFamily M ∧ IsMaximum algebraicFamily M ∧
    (logSupport M).Connected ∧
    ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j :=
  lemma41 algebraicFamily singletonAlgebraicClosure ⟨1, unitAdmissible⟩

-- The five-edge signature counts each of the four internal assignments once.
example (i j : Bool) : TwoTerminal.signature TwoTerminal.wheatstone
    (fun _ _ : Bool => (1 : ℝ)) (fun _ => 1) i j = 4 := by
  norm_num [TwoTerminal.signature_wheatstone]

-- Signed internal contributions can cancel; no positivity is built into gadget semantics.
example : TwoTerminal.signature TwoTerminal.wheatstone
    (fun i j : Bool => if i=j then (1 : ℝ) else -1) (fun _ => 1) false true = 0 := by
  norm_num [TwoTerminal.signature_wheatstone, Fintype.sum_bool]

#print axioms ClosedMatrixFamily.lemma41
#print axioms ClosedMatrixFamily.lemma43
#print axioms ClosedMatrixFamily.lemma42_structural
#print axioms ClosedMatrixFamily.lemma44
#print axioms TwoTerminal.wheatstone_planarEdgeGadget
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma42_uniform
#print axioms UniformMatrixPowerSimulation.reduction
