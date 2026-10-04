import PlanarHom.ProductInterpolationPreparationMachines
import PlanarHom.GraphNonadaptiveReduction

/-! Actual metadata, positive query batches and recovery for matrix-family
interpolation. The graph transformer is supplied as a proved ordinary TM2
computer; the final spectral instance uses the concrete path compiler. -/
noncomputable section
namespace PlanarHom.MatrixFamilyInterpolationMachines
open Complexity Complexity.MixedCode ProductInterpolationPreparationMachines
open GraphInterpolationQueries
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {t dimension : ℕ}

def preparation (A B : Fin t → K) (selected : ℕ)
    (transform : ℕ → MixedCode → MixedCode) (g : MixedCode) : Ctx A × List MixedCode :=
  (metadataFor A B (g.markedCount selected), queries transform
    ((ExponentProductTables.representatives A B (g.markedCount selected)).length, g))

/-- The number and order of queries come from the computed nonzero source
representatives, never a freely supplied enumeration or class map. -/
theorem fp_preparation (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t → K) (selected : ℕ) (transform : ℕ → MixedCode → MixedCode)
    (ht : FP inputEncoding MixedCode.encoding (fun p => transform p.1 p.2)) :
    FP MixedCode.encoding ((metadataEncoding basis A).prod MixedCode.encoding.list)
      (preparation A B selected transform) :=
  (((MixedCode.fp_unaryMarkedCount selected).comp (fp_metadataFor basis A B)).pair
    (((fp_binaryQueryCount basis A B selected).pair (fp_id MixedCode.encoding)).comp
      (fp_queries transform ht)))

/-- Every submitted query has a positive length bounded by the actual table
size, including the empty-table case when there are no submitted queries. -/
theorem query_mem {A B : Fin t → K} {selected : ℕ} {transform : ℕ → MixedCode → MixedCode}
    {g query : MixedCode} (h : query ∈ (preparation A B selected transform g).2) :
    ∃ n, 1 ≤ n ∧ n ≤ (ExponentProductTables.representatives A B (g.markedCount selected)).length ∧
      query = transform n g := mem_queries h

/-- Assemble a concrete family-interpolation caller from its actual transformer
and proved partition recovery identity. All source communication is charged. -/
def reductionOn {q bt ut bs us : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t → K) (selected : ℕ) (transform : ℕ → MixedCode → MixedCode)
    (ht : FP inputEncoding MixedCode.encoding (fun p => transform p.1 p.2))
    (MT : Fin bt → Matrix (Fin q) (Fin q) K) (UT : Fin ut → Fin q → K) (wT : Fin q → K)
    (MS : Fin bs → Matrix (Fin q) (Fin q) K) (US : Fin us → Fin q → K) (wS : Fin q → K)
    (HT HS : MixedCode → Prop)
    (validT : ∀ g, HT g → g.Valid bt ut) (validS : ∀ g, HS g → g.Valid bs us)
    (hquery : ∀ g, HT g → ∀ n, 1 ≤ n → HS (transform n g))
    (hcorrect : ∀ g (hg : HT g),
      recoverContext A ((preparation A B selected transform g).1,
        (preparation A B selected transform g).2.map (totalEvaluation MS US wS)) =
        g.evaluate (validT g hg) MT UT wT) :
    PromisePolyTimeTuringReduction (restrictedEvaluationProblem basis MT UT wT HT)
      (restrictedEvaluationProblem basis MS US wS HS) := by
  apply reductionOfPipeline basis (metadataEncoding basis A) MT UT wT MS US wS HT HS validT validS
    (preparation A B selected transform) (recoverContext A)
    (fp_preparation basis A B selected transform ht) (fp_recover_context basis A)
  · intro g hg query hq
    obtain ⟨n, hn, _, rfl⟩ := query_mem hq
    exact hquery g hg n hn
  · exact hcorrect

end PlanarHom.MatrixFamilyInterpolationMachines
