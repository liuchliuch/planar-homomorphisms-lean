import PlanarHom.ParameterizedMatrixFamilyPreparation
import PlanarHom.ParameterizedMatrixEvaluation
import PlanarHom.DynamicMatrixFamilyReduction

/-! The uniform runtime-target-parameter part of Lemma 3.10 over one fixed number field. -/
noncomputable section
namespace PlanarHom.ParameterizedMatrixFamilyReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases
open PlanarHom.MachineComposition
variable {X K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut : ℕ}

/-- The semantic view preserves the complete canonical-parameter/raw-graph word.
Its actual normalization is performed by the machine, not this proof choice. -/
private def rawView (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop) (raw : Bits)
    (h : (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).valid raw) :
    X × BitEncoding.ValidWord MixedCode.encoding := Classical.choose h

omit [DecidableEq K] in
private theorem rawView_spec (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop) (raw : Bits)
    (h : (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).valid raw) :
    (ParameterizedMatrixEvaluation.inputEncoding ex).encode (rawView basis ex M U w B allowed raw h) = raw ∧
      allowed (rawView basis ex M U w B allowed raw h).1 ∧
      (rawView basis ex M U w B allowed raw h).2.value.PlanarValid (bt+1) ut :=
  Classical.choose_spec h

/-- Actual uniform interpolation with B evaluated on the runtime parameter word.
The fixed source family, fixed field, original source answer codec and original
source simulator are retained. Candidate count depends only on marked length.
Parameter words are canonical under ex; all successfully decoded raw graph words
remain admitted, as characterized by ParameterizedMatrixEvaluation.valid_iff_rawGraph. -/
def interpolationReduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    PromisePolyTimeTuringReduction (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed)
      (DynamicMatrixFamilySource.problem basis M U w F) := by
  let normalization := Classical.choice (ParameterizedMatrixEvaluation.fp_normalize ex)
  let pre := composeComputers normalization
    (Classical.choice (ParameterizedMatrixFamilyPreparation.fp_preparation basis ex F B n₀ c bt hF hB))
  let post := Classical.choice (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  apply nonadaptiveReduction (p := simulation.outputPolynomial) (ParameterizedMatrixEvaluation.inputEncoding ex)
    (DynamicMatrixFamilyPreparation.tableEncoding basis) DynamicMatrixFamilySource.queryEncoding
    (numberFieldEncoding basis) (numberFieldEncoding basis)
    (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed)
    (DynamicMatrixFamilySource.problem basis M U w F)
    (fun p => ParameterizedMatrixFamilyPreparation.preparation F B n₀ c bt (p.1,p.2.value))
    (DynamicMatrixFamilySource.answer M U w F) MaterializedLagrangeRecoveryMachines.recover pre post
    (rawView basis ex M U w B allowed)
    (fun raw h => (rawView_spec basis ex M U w B allowed raw h).1)
  · intro raw h query hquery
    let p := rawView basis ex M U w B allowed raw h
    have hp := rawView_spec basis ex M U w B allowed raw h
    change query ∈ (DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).2 at hquery
    obtain ⟨k, _hk, _hb, rfl⟩ := DynamicMatrixFamilyPreparation.query_mem hquery
    have hs := DynamicMatrixFamilyPreparation.sample_spec F (B p.1) n₀ c bt p.2.value (hSample p.1 hp.2.1 _)
    exact DynamicMatrixFamilySource.encoded_valid basis M U w F _ _ (hn₀.trans hs.1)
      (hp.2.2.parallelLabel bt k)
  · intro query _hquery
    exact DynamicMatrixFamilySource.value_encode basis M U w F query
  · intro raw h
    let p := rawView basis ex M U w B allowed raw h
    have hp := rawView_spec basis ex M U w B allowed raw h
    have hc := DynamicMatrixFamilyRecovery.preparation_recovery_correct M U w F (B p.1) n₀ c
      hNonzero (hSample p.1 hp.2.1) p.2.value hp.2.2.1
    change (numberFieldEncoding basis).encode
      (MaterializedLagrangeRecoveryMachines.recover
        ((DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).1,
         (DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c bt p.2.value).2.map
           (DynamicMatrixFamilySource.answer M U w F))) =
      (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).value raw
    rw [hc]
    have hv := ParameterizedMatrixEvaluation.value_raw_input basis ex M U w B allowed p
    rw [show (ParameterizedMatrixEvaluation.inputEncoding ex).encode p = raw from hp.1] at hv
    rw [hv]
    congr 1
    exact (totalEvaluation_valid (appendOne M (B p.1)) U w p.2.value hp.2.2.1).symm
  · exact simulation.output_length_bound

/-- Uniform same-field target-parameter availability, obtained by composing the
actual interpolation caller with the one original family simulator. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    PromisePolyTimeTuringReduction (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed) base :=
  (interpolationReduction basis ex M U w F B allowed n₀ hn₀ c hF hB hNonzero hSample base simulation).trans simulation

end PlanarHom.ParameterizedMatrixFamilyReduction
