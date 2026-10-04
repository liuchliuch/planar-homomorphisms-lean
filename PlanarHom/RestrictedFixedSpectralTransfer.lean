import PlanarHom.RestrictedMatrixFamilyReduction
import PlanarHom.EffectiveSpectralTransfer

/-! Fixed-target effective spectral transfer on a semantic graph restriction.
This is the full raw-word compiler, specialized without adding a target parameter
to the input. Its restriction must preserve selected-label parallel copies. -/
noncomputable section
namespace PlanarHom.RestrictedFixedSpectralTransfer
open Complexity Complexity.MixedCode FiniteLanguageAliases DynamicMatrixFamilyPreparation
open PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut : ℕ}

private def rawView (H : MixedCode → Prop) (raw : Bits)
    (h : ∃ g, encoding.decode raw = some g ∧ H g) : BitEncoding.ValidWord encoding :=
  ⟨raw, by obtain ⟨g, hd, _⟩ := h; exact ⟨g, hd⟩⟩

private theorem rawView_property (H : MixedCode → Prop) (raw : Bits)
    (h : ∃ g, encoding.decode raw = some g ∧ H g) : H (rawView H raw h).value := by
  obtain ⟨g, hd, hg⟩ := h
  have hv : (rawView H raw ⟨g, hd, hg⟩).value = g := BitEncoding.ValidWord.value_eq hd
  rw [hv]
  exact hg

/-- The materialized fixed-target interpolation algorithm on exactly the supplied
raw graph promise, composed with the supplied uniform family simulator. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem basis M U w F H) base) :
    PromisePolyTimeTuringReduction (restrictedEvaluationProblem basis (appendOne M B) U w H) base := by
  let pre := composeComputers MixedCode.normalizer
    (Classical.choice (fp_preparation basis F B n₀ c bt hF))
  let post := Classical.choice (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  let first : PromisePolyTimeTuringReduction
      (restrictedEvaluationProblem basis (appendOne M B) U w H)
      (RestrictedMatrixFamilyReduction.sourceProblem basis M U w F H) := by
    apply nonadaptiveReduction (p := simulation.outputPolynomial)
      (BitEncoding.ValidWord.encoding encoding) (tableEncoding basis)
      DynamicMatrixFamilySource.queryEncoding (numberFieldEncoding basis) (numberFieldEncoding basis)
      (restrictedEvaluationProblem basis (appendOne M B) U w H)
      (RestrictedMatrixFamilyReduction.sourceProblem basis M U w F H)
      (preparation F B n₀ c bt ∘ BitEncoding.ValidWord.value)
      (DynamicMatrixFamilySource.answer M U w F) MaterializedLagrangeRecoveryMachines.recover
      pre post (rawView H) (fun _ _ => rfl)
    · intro raw h query hquery
      have hg := rawView_property H raw h
      obtain ⟨k, _, _, rfl⟩ := query_mem hquery
      have hs := sample_spec F B n₀ c bt (rawView H raw h).value (hSample _)
      exact ⟨_, DynamicMatrixFamilySource.queryEncoding.decode_encode _, hn₀.trans hs.1,
        hparallel _ hg k⟩
    · intro query _
      exact DynamicMatrixFamilySource.value_encode basis M U w F query
    · intro raw h
      have hg := rawView_property H raw h
      have hc := DynamicMatrixFamilyRecovery.preparation_recovery_correct M U w F B n₀ c
        hNonzero hSample (rawView H raw h).value (hvalid _ hg)
      change (numberFieldEncoding basis).encode
        (MaterializedLagrangeRecoveryMachines.recover
          ((preparation F B n₀ c bt (rawView H raw h).value).1,
           (preparation F B n₀ c bt (rawView H raw h).value).2.map
             (DynamicMatrixFamilySource.answer M U w F))) = _
      rw [hc]
      exact (evaluationValue_decode basis (appendOne M B) U w raw (rawView H raw h).value
        (BitEncoding.ValidWord.decode_raw (rawView H raw h)) (hvalid _ hg)).symm
    · exact simulation.output_length_bound
  exact first.trans simulation

end PlanarHom.RestrictedFixedSpectralTransfer
