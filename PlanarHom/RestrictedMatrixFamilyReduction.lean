import PlanarHom.ParameterizedMatrixFamilyReduction

/-! The actual uniform fixed-field caller on a semantic graph restriction that
is preserved by selected-label thickening, including intrinsic prescribed domains. -/
noncomputable section
namespace PlanarHom.RestrictedMatrixFamilyReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PlanarHom.MachineComposition
variable {X K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut : ℕ}

def sourceProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (H : MixedCode → Prop) : PromiseProblem :=
  ⟨fun raw => ∃ p : ℕ × MixedCode, DynamicMatrixFamilySource.queryEncoding.decode raw = some p ∧
      1 ≤ p.1 ∧ H p.2,
    (DynamicMatrixFamilySource.problem basis M U w F).value⟩

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop) (H : MixedCode → Prop) : PromiseProblem :=
  ⟨fun raw => ∃ p : X × BitEncoding.ValidWord MixedCode.encoding,
      (ParameterizedMatrixEvaluation.inputEncoding ex).encode p = raw ∧ allowed p.1 ∧ H p.2.value,
    (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).value⟩

/-- All restrictions are checked as semantic source promises; the actual machine
uses the already proved raw normalization/search/query/recovery pipeline. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (sourceProblem basis M U w F H) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U w B allowed H) base := by
  let pre := composeComputers (Classical.choice (ParameterizedMatrixEvaluation.fp_normalize ex))
    (Classical.choice (ParameterizedMatrixFamilyPreparation.fp_preparation basis ex F B n₀ c bt hF hB))
  let post := Classical.choice (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  let view : ∀ raw, (targetProblem basis ex M U w B allowed H).valid raw →
      X × BitEncoding.ValidWord MixedCode.encoding := fun raw h => Classical.choose h
  have hv (raw) (h : (targetProblem basis ex M U w B allowed H).valid raw) :
      (ParameterizedMatrixEvaluation.inputEncoding ex).encode (view raw h) = raw ∧
        allowed (view raw h).1 ∧ H (view raw h).2.value := Classical.choose_spec h
  let first : PromisePolyTimeTuringReduction (targetProblem basis ex M U w B allowed H)
      (sourceProblem basis M U w F H) := by
    apply nonadaptiveReduction (p := simulation.outputPolynomial)
      (ParameterizedMatrixEvaluation.inputEncoding ex) (DynamicMatrixFamilyPreparation.tableEncoding basis)
      DynamicMatrixFamilySource.queryEncoding (numberFieldEncoding basis) (numberFieldEncoding basis)
      (targetProblem basis ex M U w B allowed H) (sourceProblem basis M U w F H)
      (fun p => ParameterizedMatrixFamilyPreparation.preparation F B n₀ c bt (p.1,p.2.value))
      (DynamicMatrixFamilySource.answer M U w F) MaterializedLagrangeRecoveryMachines.recover
      pre post view (fun raw h => (hv raw h).1)
    · intro raw h query hquery
      let p := view raw h
      have hp := hv raw h
      change query ∈ (DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).2 at hquery
      obtain ⟨k, _, _, rfl⟩ := DynamicMatrixFamilyPreparation.query_mem hquery
      have hs := DynamicMatrixFamilyPreparation.sample_spec F (B p.1) n₀ c bt p.2.value (hSample p.1 hp.2.1 _)
      exact ⟨_, DynamicMatrixFamilySource.queryEncoding.decode_encode _, hn₀.trans hs.1,
        hparallel p.2.value hp.2.2 k⟩
    · intro query _
      exact DynamicMatrixFamilySource.value_encode basis M U w F query
    · intro raw h
      let p := view raw h
      have hp := hv raw h
      have hc := DynamicMatrixFamilyRecovery.preparation_recovery_correct M U w F (B p.1) n₀ c
        hNonzero (hSample p.1 hp.2.1) p.2.value (hvalid _ hp.2.2)
      change (numberFieldEncoding basis).encode
        (MaterializedLagrangeRecoveryMachines.recover
          ((DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).1,
           (DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).2.map
            (DynamicMatrixFamilySource.answer M U w F))) = _
      rw [hc]
      have hz := ParameterizedMatrixEvaluation.value_raw_input basis ex M U w B allowed p
      rw [show (ParameterizedMatrixEvaluation.inputEncoding ex).encode p = raw from hp.1] at hz
      change _ = (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).value raw
      rw [hz]
      congr 1
      exact (totalEvaluation_valid (appendOne M (B p.1)) U w p.2.value (hvalid _ hp.2.2)).symm
    · exact simulation.output_length_bound
  exact first.trans simulation

end PlanarHom.RestrictedMatrixFamilyReduction
