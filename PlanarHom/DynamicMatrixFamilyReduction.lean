import PlanarHom.DynamicMatrixFamilyRecovery
import PlanarHom.SourceSimulationOutputBounds
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.OracleReductionComposition
import PlanarHom.PlanarRibbonExistence

/-! A genuine uniform fixed-field interpolation compiler for source Lemma 3.10. -/
noncomputable section
namespace PlanarHom.DynamicMatrixFamilyReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases DynamicMatrixFamilyPreparation
open PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut : ℕ}

private def rawView (raw : Bits) (h : MixedCode.PlanarInput (bt+1) ut raw) :
    BitEncoding.ValidWord MixedCode.encoding :=
  ⟨raw, by obtain ⟨g, hd, _⟩ := h; exact ⟨g, hd⟩⟩

private theorem rawView_planar (raw : Bits) (h : MixedCode.PlanarInput (bt+1) ut raw) :
    (rawView raw h).value.PlanarValid (bt+1) ut := by
  obtain ⟨g, hd, hg⟩ := h
  have hv : (rawView raw ⟨g,hd,hg⟩).value = g := BitEncoding.ValidWord.value_eq hd
  rw [hv]
  exact hg

/-- Actual preprocessing, tagged family queries, and total materialized recovery.
The source answer-length polynomial is derived from the supplied real simulation;
there is no assumed dynamic arithmetic or oracle-output bound. -/
def interpolationReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M B) U w)
      (DynamicMatrixFamilySource.problem basis M U w F) := by
  let pre := composeComputers MixedCode.normalizer
    (Classical.choice (fp_preparation basis F B n₀ c bt hF))
  let post := Classical.choice (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  apply nonadaptiveReduction (p := simulation.outputPolynomial) (BitEncoding.ValidWord.encoding MixedCode.encoding)
    (tableEncoding basis) DynamicMatrixFamilySource.queryEncoding (numberFieldEncoding basis)
    (numberFieldEncoding basis) (evaluationProblem basis (appendOne M B) U w)
    (DynamicMatrixFamilySource.problem basis M U w F)
    (preparation F B n₀ c bt ∘ BitEncoding.ValidWord.value)
    (DynamicMatrixFamilySource.answer M U w F) MaterializedLagrangeRecoveryMachines.recover pre post
    rawView (fun _ _ => rfl)
  · intro raw h query hquery
    have hg := rawView_planar raw h
    obtain ⟨k, _hk, _hb, rfl⟩ := query_mem hquery
    have hs := sample_spec F B n₀ c bt (rawView raw h).value (hSample _)
    exact DynamicMatrixFamilySource.encoded_valid basis M U w F _ _ (hn₀.trans hs.1)
      (hg.parallelLabel bt k)
  · intro query _hquery
    exact DynamicMatrixFamilySource.value_encode basis M U w F query
  · intro raw h
    have hg := rawView_planar raw h
    have hc := DynamicMatrixFamilyRecovery.preparation_recovery_correct M U w F B n₀ c hNonzero hSample
      (rawView raw h).value hg.1
    change (numberFieldEncoding basis).encode
      (MaterializedLagrangeRecoveryMachines.recover
        ((preparation F B n₀ c bt (rawView raw h).value).1,
         (preparation F B n₀ c bt (rawView raw h).value).2.map (DynamicMatrixFamilySource.answer M U w F))) =
      evaluationValue basis (appendOne M B) U w raw
    rw [hc]
    exact (evaluationValue_decode basis (appendOne M B) U w raw (rawView raw h).value
      (BitEncoding.ValidWord.decode_raw (rawView raw h)) hg.1).symm
  · exact simulation.output_length_bound

/-- The final source-(ii) composition: every family query is implemented by the
same supplied source simulator, preserving its oracle and exact answer codec. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M B) U w) base :=
  (interpolationReduction basis M U w F B n₀ hn₀ c hF hNonzero hSample base simulation).trans simulation

end PlanarHom.DynamicMatrixFamilyReduction
