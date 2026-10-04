import PlanarHom.MainStructuralSupportTransport
import PlanarHom.MainSourceQuotientFacts
import PlanarHom.PositiveWeightedComponentNecessityConditional
import PlanarHom.NonnegativeSupportShapesBasic
import PlanarHom.MainTractabilityConditional
import PlanarHom.WeightedBlockTractabilityQuotientConditional
import PlanarHom.PositiveDichotomyAssemblyConditional
import PlanarHom.PositivePottsInterface
import PlanarHom.RectangularUnweightedSourceFormsConditional
import PlanarHom.PositiveRealCoreClassObstruction
import PlanarHom.BooleanTensorEasyAssembly

/-! Main transport with explicit Potts/Ising parameters.
`MainDichotomiesClosed` instantiates these parameters with the proved foundations. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode RootedRestriction Structures
variable {q r : ℕ}

/-- Positive source8.1 gives the exact allowed block with the independent
Potts hardness premise explicit at this intermediate layer. -/
theorem main_positive_block_of_not_hard_of_potts (hPotts : PositivePottsFoundation) [Nonempty (Fin q)]
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hp : ∀ i j,0<L.matrices 0 i j) (hn : ¬PromisedSharpPHard L.problem) :
    AllowedBlock (L.matrices 0) := by
  obtain ⟨k,d,e,a,ρ,hk,ha,hρ,hM⟩ :=
    L.positiveTensorForm_of_not_hard hPotts 0 hunit hs hp hn
  refine .positive k d hk a ρ ha hρ e ?_
  intro i j
  have h := congrFun (congrFun hM (e i)) (e j)
  simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply] using h

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
namespace PlanarHom.RectangularUnweightedSourceForms
open Structures Boolean RectangularSourceNormSimulation

/-- The rectangular display is the literal allowed bipartite block. -/
theorem allowedBlock_of_form {p s : ℕ} (V : Matrix (Fin p) (Fin s) ℝ)
    (hf : RectangularTensorForm V) : AllowedBlock (block V) := by
  obtain ⟨k,l,d,eX,eY,a,b,ρ,hk,hl,ha,hb,hρ,hV⟩ := hf
  refine .bipartite k l d hk hl a b ρ ha hb hρ (colorChart eX eY) ?_
  intro i j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
    simp [block,colorChart,sumProductEquiv,bipartiteAmplitude,hV,tensor_symm]

end PlanarHom.RectangularUnweightedSourceForms
namespace PlanarHom.NonnegativeSupportShapes
open RectangularSourceNormSimulation

/-- The support-derived arbitrary finite bipartition is the literal finite-sum
block used by the rectangular source compiler, including unequal side sizes. -/
theorem double_finSum {p s : ℕ} (V : Matrix (Fin p) (Fin s) ℝ) (i j : Fin (p+s)) :
    double V (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)=block V i j := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;> simp [double,block]

end PlanarHom.NonnegativeSupportShapes
