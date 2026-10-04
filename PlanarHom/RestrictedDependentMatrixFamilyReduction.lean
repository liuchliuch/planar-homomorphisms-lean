import PlanarHom.DependentMatrixFamilyReduction
import PlanarHom.RestrictedMatrixFamilyReduction

/-! The actual variable-field caller on a semantic graph predicate preserved by thickening. -/
noncomputable section
namespace PlanarHom.RestrictedDependentMatrixFamilyReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases MachineComposition
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
variable {sourceDimension q bt ut : ℕ}

def targetProblem (ex : BitEncoding X) (output : ∀ x, BitEncoding (K x)) (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop) (H : MixedCode → Prop) : PromiseProblem :=
  ⟨fun raw => ∃ p : X × BitEncoding.ValidWord MixedCode.encoding,
      (DependentMatrixEvaluation.inputEncoding ex).encode p = raw ∧ allowed p.1 ∧ H p.2.value,
    (DependentMatrixEvaluation.problem K ex output inclusion M U w B allowed).value⟩

/-- This is a compiled caller, not an assumed reduction rule. Source (b) is
represented by actual uniform presentation, addition, multiplication and inclusion
machines; source (c) by hB. Bit growth is derived from hpresentation and the fixed
degree bound. The prescribed target output conversion is explicitly houtput.
All source queries and source answers keep the original fixed-field codecs. -/
def interpolationReduction
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x) (output : ∀ x, BitEncoding (K x))
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (candidates : Polynomial ℕ)
    (degreeBound : ℕ) (degree_le : ∀ x, dimension x ≤ degreeBound)
    (hpresentation : FP ex BitEncoding.rat.list
      (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (houtput : FP (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      BitEncoding.bits (fun s : Σ x, K x => (output s.1).encode s.2))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H) base) :
    PromisePolyTimeTuringReduction (targetProblem K ex output inclusion M U w B allowed H)
      (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H) := by
  let ec := DependentMatrixFamilyPreparation.contextEncoding sourceBasis ex
  let ey := numberFieldEncoding sourceBasis
  let recover := fun p : (((X × ℕ) × List (L × List ℕ)) × List L) =>
    DependentTargetAggregation.recover K inclusion (fun x => binaryAlphabet (B x))
      (p.1.1,(p.1.2,p.2))
  let postprocess := fun p : (((X × ℕ) × List (L × List ℕ)) × List L) =>
    (output (recover p).1).encode (recover p).2
  have htest := CrossFieldCollisionMachines.fp_test sourceBasis ex K dimension basis inclusion
    (fun x => binaryAlphabet (B x)) degreeBound degree_le hpresentation hmul hinclusion hB
  let normalization := Classical.choice (ParameterizedMatrixEvaluation.fp_normalize ex)
  let pre := composeComputers normalization
    (Classical.choice (DependentMatrixFamilyPreparation.fp_preparation K F B n₀ candidates bt
      sourceBasis ex hF htest))
  have hp := PairProjectionMachines.fp_fst ec ey.list
  have hx := hp.comp (PairProjectionMachines.fp_fst (ex.prod BitEncoding.unaryNat)
    (SourceExponentRepresentatives.rowEncoding sourceBasis).list)
  have hr := hp.comp (PairProjectionMachines.fp_snd (ex.prod BitEncoding.unaryNat)
    (SourceExponentRepresentatives.rowEncoding sourceBasis).list)
  have hy := PairProjectionMachines.fp_snd ec ey.list
  have hrecover : FP (ec.prod ey.list)
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) recover :=
    (hx.pair (hr.pair hy)).comp (DependentTargetAggregation.fp_recover sourceBasis ex K dimension basis inclusion
      (fun x => binaryAlphabet (B x)) degreeBound degree_le hpresentation hmul hadd hinclusion hB)
  let post := Classical.choice (hrecover.comp houtput)
  let target := targetProblem K ex output inclusion M U w B allowed H
  let view := fun raw (h : target.valid raw) => Classical.choose h
  have hview (raw : Bits) (h : target.valid raw) :
      (DependentMatrixEvaluation.inputEncoding ex).encode (view raw h) = raw ∧
      allowed (view raw h).1 ∧ H (view raw h).2.value := Classical.choose_spec h
  apply nonadaptiveReduction (p := simulation.outputPolynomial) (DependentMatrixEvaluation.inputEncoding ex)
    ec DynamicMatrixFamilySource.queryEncoding ey BitEncoding.bits target
    (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H)
    (fun p => DependentMatrixFamilyPreparation.preparation K F B n₀ candidates bt (p.1,p.2.value))
    (DynamicMatrixFamilySource.answer M U w F) postprocess pre post view
    (fun raw h => (hview raw h).1)
  · intro raw h query hquery
    let p := view raw h
    have hv := hview raw h
    obtain ⟨k,_hk,_hb,rfl⟩ := DependentMatrixFamilyPreparation.query_mem K F B n₀ candidates bt hquery
    have hs := DependentMatrixFamilyPreparation.sample_spec K F B n₀ candidates bt
      (p.1,p.2.value) (hSample p.1 hv.2.1 _)
    exact ⟨_,DynamicMatrixFamilySource.queryEncoding.decode_encode _,hn₀.trans hs.1,
      hparallel p.2.value hv.2.2 k⟩
  · intro query _hquery
    exact DynamicMatrixFamilySource.value_encode sourceBasis M U w F query
  · intro raw h
    let p := view raw h
    have hv := hview raw h
    have hc := DependentMatrixFamilyRecovery.preparation_recovery_correct K inclusion M U w F B
      n₀ candidates hNonzero p.1 (hSample p.1 hv.2.1) p.2.value (hvalid _ hv.2.2)
    change (output (recover _).1).encode (recover _).2 = target.value raw
    have he : recover
        ((DependentMatrixFamilyPreparation.preparation K F B n₀ candidates bt (p.1,p.2.value)).1,
         (DependentMatrixFamilyPreparation.preparation K F B n₀ candidates bt (p.1,p.2.value)).2.map
           (DynamicMatrixFamilySource.answer M U w F)) =
        ⟨p.1,p.2.value.evaluate (hvalid _ hv.2.2) (appendOne (fun l i j => inclusion p.1 (M l i j)) (B p.1))
          (fun l i => inclusion p.1 (U l i)) (fun i => inclusion p.1 (w i))⟩ := hc
    rw [he]
    have hout := DependentMatrixEvaluation.value_raw_input K ex output inclusion M U w B allowed p
    rw [show (DependentMatrixEvaluation.inputEncoding ex).encode p = raw from hv.1] at hout
    change _ = (DependentMatrixEvaluation.problem K ex output inclusion M U w B allowed).value raw
    rw [hout]
    unfold DependentMatrixEvaluation.answer
    rw [totalEvaluation_valid _ _ _ _ (hvalid _ hv.2.2)]
  · exact simulation.output_length_bound

/-- Composition with the original uniform source simulator gives the final
variable-field target-to-base reduction, including m = 0. -/
def reduction
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x) (output : ∀ x, BitEncoding (K x))
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (candidates : Polynomial ℕ)
    (degreeBound : ℕ) (degree_le : ∀ x, dimension x ≤ degreeBound)
    (hpresentation : FP ex BitEncoding.rat.list
      (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (houtput : FP (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      BitEncoding.bits (fun s : Σ x, K x => (output s.1).encode s.2))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H) base) :
    PromisePolyTimeTuringReduction (targetProblem K ex output inclusion M U w B allowed H) base :=
  (interpolationReduction K sourceBasis ex dimension basis inclusion output M U w F B allowed H hvalid hparallel n₀ hn₀ candidates
    degreeBound degree_le hpresentation hmul hadd hinclusion hF hB houtput hNonzero hSample base simulation).trans simulation

/-- Direct canonical-payload endpoint: no output-conversion assumption remains.
The parameter frame is removed by the explicit actual projection machine. -/
def canonicalReduction
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (candidates : Polynomial ℕ)
    (degreeBound : ℕ) (degree_le : ∀ x, dimension x ≤ degreeBound)
    (hpresentation : FP ex BitEncoding.rat.list
      (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H) base) :
    PromisePolyTimeTuringReduction
      (targetProblem K ex (fun x => numberFieldEncoding (basis x)) inclusion M U w B allowed H) base :=
  reduction K sourceBasis ex dimension basis inclusion (fun x => numberFieldEncoding (basis x)) M U w F B allowed H hvalid hparallel
    n₀ hn₀ candidates degreeBound degree_le hpresentation hmul hadd hinclusion hF hB
    (DependentEncodingMachines.fp_payload ex (DependentFieldListMachines.fieldEncoding K dimension basis))
    hNonzero hSample base simulation

end PlanarHom.RestrictedDependentMatrixFamilyReduction
