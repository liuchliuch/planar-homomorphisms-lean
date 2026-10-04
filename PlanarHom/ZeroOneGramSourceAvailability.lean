-- Recovered Gram proof bodies; support helpers are imported from their checked extraction.
import PlanarHom.AlgebraicLanguageExtensions
import PlanarHom.ContextualGadgetClosure
import PlanarHom.WeightedGramAvailability
import PlanarHom.RootedRealComponentAvailability
import PlanarHom.ActualTwinReduction
import PlanarHom.MainSupportFiniteSource

/-! Actual original-source availability of the Section 7 Gram matrix and its
literal finite support blocks. Canonical fields are converted by real machines;
component colours are reindexed without changing the raw graph promise. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval
variable {q : ℕ}

def gramMatrix (L : RealLanguage q 1 0) (p : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  gramCoreField (L.matrices 0) L.weights p

theorem gramMatrix_coe (L : RealLanguage q 1 0) (p : ℕ) (i j : Fin q) :
    ((gramCoreField (L.matricesK 0) L.weightsK p i j : L.field) : ℝ)=L.gramMatrix p i j := by
  simp [gramMatrix,gramCoreField,Matrix.mul_apply,Matrix.diagonal_apply]

theorem gramMatrix_algebraic (L : RealLanguage q 1 0) (p : ℕ) (i j : Fin q) :
    IsAlgebraic ℚ (L.gramMatrix p i j) := by
  rw [←L.gramMatrix_coe p i j]
  exact (IsAlgebraic.of_finite ℚ (gramCoreField (L.matricesK 0) L.weightsK p i j)).algHom L.field.val

def gramLanguage (L : RealLanguage q 1 0) (p : ℕ) : RealLanguage q 1 0 :=
  unitLanguage (fun _=>L.gramMatrix p) (fun _=>L.gramMatrix_algebraic p)

def gramSourceReduction (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1) (p : ℕ) :
    PromisePolyTimeTuringReduction (L.gramLanguage p).problem L.problem := by
  let T := L.appendBinary (L.gramMatrix p) (L.gramMatrix_algebraic p)
  have r₁ := (L.gramLanguage p).relabelReduction T (fun _=>Fin.last 1) (fun u=>u.elim0)
    (fun _ i j=>(congrFun (congrFun (appendOne_aux L.matrices (L.gramMatrix p)) i) j).symm)
    (fun u=>u.elim0) (fun i=>(hunit i).symm)
  have r₂ := L.appendBinaryRealizationReduction (L.gramMatrix p) (L.gramMatrix_algebraic p)
    L.field L.basis L.matricesK L.unariesK L.weightsK
    (gramCoreField (L.matricesK 0) L.weightsK p)
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl) (L.gramMatrix_coe p)
  exact r₁.trans (r₂.trans (gramAppendReduction L.basis L.matricesK L.unariesK L.weightsK 0 p))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
