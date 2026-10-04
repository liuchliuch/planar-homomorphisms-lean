import PlanarHom.RestrictedMatrixFamilyReduction
import PlanarHom.UniformMatrixPowerSimulation

/-! Uniform power substitution on exact graph promises, allowing source and
target intrinsic-domain records to differ only at new internal vertices. -/
noncomputable section
namespace PlanarHom.UniformMatrixPowerRestriction
open Complexity Complexity.MixedCode FiniteLanguageAliases PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut : ℕ}

def reductionOn (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (HT HS : MixedCode → Prop)
    (validT : ∀ g, HT g → g.Valid (bt+1) ut) (validS : ∀ g, HS g → g.Valid bt ut)
    (transform : ℕ → MixedCode → MixedCode)
    (hfp : FP DynamicMatrixFamilySource.queryEncoding MixedCode.encoding (fun p => transform p.1 p.2))
    (hquery : ∀ g, HT g → ∀ n, 1 ≤ n → HS (transform n g))
    (hcorrect : ∀ g (hg : HT g) n (hn : 1 ≤ n),
      (transform n g).evaluate (validS _ (hquery g hg n hn)) M U (fun _ => 1) =
        g.evaluate (validT g hg) (appendOne M (M old ^ n)) U (fun _ => 1)) :
    PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem basis M U (fun _ => 1) (fun n => M old ^ n) HT)
      (restrictedEvaluationProblem basis M U (fun _ => 1) HS) := by
  let prep : ℕ × MixedCode → Bits × List MixedCode := fun p => ([],[transform p.1 p.2])
  have hp : FP DynamicMatrixFamilySource.queryEncoding (BitEncoding.bits.prod MixedCode.encoding.list) prep :=
    (fp_const _ BitEncoding.bits []).pair
      ((hfp.pair (fp_const _ MixedCode.encoding.list [])).comp (ListMutationMachines.fp_cons _))
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis)
      (UniformMatrixPowerSimulation.recover : Bits × List K → K) :=
    (PairProjectionMachines.fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  let pre := composeComputers (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer MixedCode.normalizer)
    (Classical.choice hp)
  let post := Classical.choice hr
  let target := RestrictedMatrixFamilyReduction.sourceProblem basis M U (fun _ => 1) (fun n => M old ^ n) HT
  let view : ∀ raw, target.valid raw → BitEncoding.ValidWord DynamicMatrixFamilySource.queryEncoding :=
    fun raw h => ⟨raw, by obtain ⟨p,hd,_⟩ := h; exact ⟨p,hd⟩⟩
  have hv (raw) (h : target.valid raw) : 1 ≤ (view raw h).value.1 ∧ HT (view raw h).value.2 := by
    obtain ⟨p,hd,hn,hg⟩ := h
    have he := BitEncoding.ValidWord.value_eq (w := view raw ⟨p,hd,hn,hg⟩) hd
    rw [he]
    exact ⟨hn,hg⟩
  let hb := PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound basis M U (fun _ => 1)
  let p := Classical.choose hb
  have hbound := Classical.choose_spec hb
  apply nonadaptiveReduction (p := p) (BitEncoding.ValidWord.encoding DynamicMatrixFamilySource.queryEncoding)
    BitEncoding.bits MixedCode.encoding (numberFieldEncoding basis) (numberFieldEncoding basis)
    target (restrictedEvaluationProblem basis M U (fun _ => 1) HS)
    (prep ∘ BitEncoding.ValidWord.value) (totalEvaluation M U (fun _ => 1))
    UniformMatrixPowerSimulation.recover pre post view (fun _ _ => rfl)
  · intro raw h query hmem
    have hs := hv raw h
    have he : query = transform (view raw h).value.1 (view raw h).value.2 := List.mem_singleton.mp hmem
    subst query
    exact ⟨_, encoding.decode_encode _, hquery _ hs.2 _ hs.1⟩
  · intro query hquery
    obtain ⟨g,hd,hg⟩ := hquery
    rw [encoding.decode_encode] at hd
    cases Option.some.inj hd
    change evaluationValue basis M U (fun _ => 1) (encoding.encode query) = _
    rw [evaluationValue_encode _ _ _ _ _ (validS _ hg), totalEvaluation_valid _ _ _ _ (validS _ hg)]
  · intro raw h
    let z := view raw h
    have hs := hv raw h
    change (numberFieldEncoding basis).encode
      ([totalEvaluation M U (fun _ => 1) (transform z.value.1 z.value.2)].sum) = _
    rw [List.sum_cons,List.sum_nil,add_zero,
      totalEvaluation_valid _ _ _ _ (validS _ (hquery _ hs.2 _ hs.1)), hcorrect _ hs.2 _ hs.1]
    have hd : DynamicMatrixFamilySource.queryEncoding.decode raw = some z.value := z.decode_raw
    change _ = (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (fun n => M old ^ n)).value raw
    simp only [DynamicMatrixFamilySource.problem,encodedFunction,hd,DynamicMatrixFamilySource.answer]
    congr 1
    exact (totalEvaluation_valid _ _ _ z.value.2 (validT _ hs.2)).symm
  · intro raw h
    obtain ⟨g,hd,hg⟩ := h
    change (evaluationValue basis M U (fun _ => 1) raw).length ≤ p.eval raw.length
    rw [evaluationValue_decode _ _ _ _ raw g hd (validS _ hg)]
    exact hbound raw g (validS _ hg) hd

end PlanarHom.UniformMatrixPowerRestriction
