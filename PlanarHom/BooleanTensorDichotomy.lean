import PlanarHom.PositiveIsingFoundationClosed
import PlanarHom.BooleanTensorHardness
import PlanarHom.UnitBackgroundLanguage

/-! NEW complete original-scope Theorem 5.1. Strictly positive algebraic PD
Boolean factors have an actual FP tensor algorithm when every diagonal pair
is equal; any unequal diagonal gives genuine promised #P hardness. Both
independent foundations are discharged. Ordinary planar inputs include loops,
parallel edges, isolates and the empty graph, with unit background weights. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorDichotomy
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open BooleanTensorEasyAssembly BooleanTensorFPClosure
variable {q d : ℕ}

theorem equal_tensor_inFP (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (e : Fin q≃Boolean.Cube d) (F : Fin d→Matrix Bool Bool ℝ)
    (hF : ∀r,(F r).PosDef) (hpos : ∀r i j,0<F r i j)
    (halg : ∀r i j,IsAlgebraic ℚ (F r i j))
    (hsource : Matrix.reindex e e (L.matrices 0)=CubeTensorExponential.tensor F)
    (hequal : ∀r,F r false false=F r true true) : L.problem.InFP := by
  have hs : ∀r,F r true false=F r false true := by
    intro r
    simpa only [star_trivial] using (hF r).1.apply false true
  have h := source_scaled_equal_tensor_inFP positiveIsingFoundation L.field L.basis
    (L.matricesK 0) e 1 isAlgebraic_one F halg hs hequal
    (fun r=>hpos r false false) (fun r=>hpos r false true)
    (by simpa only [one_smul] using hsource)
  have hm : (fun _ : Fin 1=>L.matricesK 0)=L.matricesK := by
    funext l
    exact congrArg L.matricesK (Fin.eq_zero l).symm
  have hu : (emptyUnaries : Fin 0→Fin q→L.field)=L.unariesK := by
    funext l
    exact l.elim0
  rw [hm,hu,←RealLanguage.weightsK_eq_one L hunit] at h
  exact h

/-- The original two alternatives, on the literal tensor and the source's
canonical exact algebraic output presentation. There is no foundation premise. -/
theorem theorem5_1 (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (e : Fin q≃Boolean.Cube d) (F : Fin d→Matrix Bool Bool ℝ)
    (hF : ∀r,(F r).PosDef) (hpos : ∀r i j,0<F r i j)
    (halg : ∀r i j,IsAlgebraic ℚ (F r i j))
    (hsource : Matrix.reindex e e (L.matrices 0)=CubeTensorExponential.tensor F) :
    ((∀r,F r false false=F r true true) → L.problem.InFP) ∧
    ((∃r,F r false false≠F r true true) → PromisedSharpPHard L.problem) := by
  constructor
  · exact equal_tensor_inFP L hunit e F hF hpos halg hsource
  · exact BooleanUnequalFactorReduction.tensor_promisedSharpPHard
      L hunit 0 e F hF hpos halg hsource

theorem tensor_entries_algebraic (F : Fin d→Matrix Bool Bool ℝ)
    (halg : ∀r i j,IsAlgebraic ℚ (F r i j)) (x y : Boolean.Cube d) :
    IsAlgebraic ℚ (CubeTensorExponential.tensor F x y) := by
  have hprod (S : Finset (Fin d)) : IsAlgebraic ℚ (∏r∈S,F r (x r) (y r)) := by
    induction S using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic ℚ (1:ℝ))
    | @insert r S hr ih =>
      simpa only [Finset.prod_insert hr] using (halg r (x r) (y r)).mul ih
  exact hprod Finset.univ

/-- The literal tensor matrix, numbered by the canonical finite cube chart. -/
def tensorLanguage (F : Fin d→Matrix Bool Bool ℝ)
    (halg : ∀r i j,IsAlgebraic ℚ (F r i j)) :
    RealLanguage (Fintype.card (Boolean.Cube d)) 1 0 :=
  RealLanguage.unitLanguage
    (fun _ i j=>CubeTensorExponential.tensor F
      ((Fintype.equivFin (Boolean.Cube d)).symm i)
      ((Fintype.equivFin (Boolean.Cube d)).symm j))
    (fun _ i j=>tensor_entries_algebraic F halg _ _)

/-- Direct original statement for N = C₁ ⊗ ⋯ ⊗ C_d. This wrapper has only
strict positivity, algebraicity and positive definiteness of the factors. -/
theorem theorem5_1_literal (F : Fin d→Matrix Bool Bool ℝ)
    (hF : ∀r,(F r).PosDef) (hpos : ∀r i j,0<F r i j)
    (halg : ∀r i j,IsAlgebraic ℚ (F r i j)) :
    ((∀r,F r false false=F r true true) → (tensorLanguage F halg).problem.InFP) ∧
    ((∃r,F r false false≠F r true true) →
      PromisedSharpPHard (tensorLanguage F halg).problem) := by
  apply theorem5_1 (tensorLanguage F halg) (fun _=>rfl)
    (Fintype.equivFin (Boolean.Cube d)).symm F hF hpos halg
  ext x y
  simp only [tensorLanguage,RealLanguage.unitLanguage,Matrix.reindex_apply,
    Matrix.submatrix_apply,Equiv.symm_symm,Equiv.symm_apply_apply]

end PlanarHom.BooleanTensorDichotomy
