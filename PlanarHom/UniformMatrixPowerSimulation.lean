import PlanarHom.DynamicMatrixFamilySource
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.SelectedStretchAppend
import PlanarHom.MaterializedFieldListMachines

/-! Source3.10(ii) for actual positive-integer matrix powers, via one uniform
path-substitution machine with the integer supplied in unary. -/
noncomputable section
namespace PlanarHom.UniformMatrixPowerSimulation
open Complexity Complexity.MixedCode FiniteLanguageAliases PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}

def prepare (bt selected : ℕ) (p : ℕ × MixedCode) : Bits × List MixedCode :=
  ([], [p.2.stretchLabelLength bt selected p.1])

def recover (p : Bits × List K) : K := p.2.sum

private def rawView (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (raw : Bits) (h : (DynamicMatrixFamilySource.problem basis M U (fun _ => 1)
      (fun n => M old ^ n)).valid raw) : BitEncoding.ValidWord DynamicMatrixFamilySource.queryEncoding :=
  ⟨raw, by obtain ⟨p, hp, _⟩ := h; exact ⟨p, hp⟩⟩

private theorem rawView_spec (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (raw : Bits) (h : (DynamicMatrixFamilySource.problem basis M U (fun _ => 1)
      (fun n => M old ^ n)).valid raw) :
    1 ≤ (rawView basis M U old raw h).value.1 ∧
      (rawView basis M U old raw h).value.2.PlanarValid (bt+1) ut := by
  obtain ⟨p, hp, hn, hg⟩ := h
  have he := BitEncoding.ValidWord.value_eq (w := rawView basis M U old raw ⟨p,hp,hn,hg⟩) hp
  rw [he]
  exact ⟨hn,hg⟩

/-- All original matrices/unaries coexist; each auxiliary power occurrence gets
its own private path, with unit weights on all new vertices. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt) :
    PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (fun n => M old ^ n))
      (evaluationProblem basis M U (fun _ => 1)) := by
  have hp : FP DynamicMatrixFamilySource.queryEncoding
      (BitEncoding.bits.prod MixedCode.encoding.list) (prepare bt old.val) := by
    have hs := ((fp_stretchLabelLength bt old.val).pair
      (fp_const DynamicMatrixFamilySource.queryEncoding MixedCode.encoding.list [])).comp
        (ListMutationMachines.fp_cons MixedCode.encoding)
    exact (fp_const DynamicMatrixFamilySource.queryEncoding BitEncoding.bits []).pair hs
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) (recover : Bits × List K → K) :=
    (PairProjectionMachines.fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  let pre := composeComputers (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer MixedCode.normalizer)
    (Classical.choice hp)
  let post := Classical.choice hr
  let hb := PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound
    basis M U (fun _ => 1)
  let p := Classical.choose hb
  have hbound := Classical.choose_spec hb
  apply nonadaptiveReduction (p := p) (BitEncoding.ValidWord.encoding DynamicMatrixFamilySource.queryEncoding)
    BitEncoding.bits MixedCode.encoding (numberFieldEncoding basis) (numberFieldEncoding basis)
    (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (fun n => M old ^ n))
    (evaluationProblem basis M U (fun _ => 1)) (prepare bt old.val ∘ BitEncoding.ValidWord.value)
    (totalEvaluation M U (fun _ => 1)) recover pre post (rawView basis M U old) (fun _ _ => rfl)
  · intro raw h query hquery
    have hs := rawView_spec basis M U old raw h
    have he : query = (rawView basis M U old raw h).value.2.stretchLabelLength
        bt old.val (rawView basis M U old raw h).value.1 := List.mem_singleton.mp hquery
    subst query
    exact ⟨_, MixedCode.encoding.decode_encode _,
      stretchLabelLength_planar _ hs.2 bt _ old (appended_companion_bound _ hs.2.1)⟩
  · intro query hquery
    obtain ⟨g, hd, hg⟩ := hquery
    rw [MixedCode.encoding.decode_encode] at hd
    cases Option.some.inj hd
    change evaluationValue basis M U (fun _ => 1) (encoding.encode query) = _
    rw [evaluationValue_encode _ _ _ _ _ hg.1, totalEvaluation_valid _ _ _ _ hg.1]
  · intro raw h
    let z := rawView basis M U old raw h
    have hs := rawView_spec basis M U old raw h
    have hv := stretchLabelLength_valid z.value.2 hs.2.1 bt z.value.1 old
      (appended_companion_bound _ hs.2.1)
    have hc := evaluate_stretchLabelLength_appendOne z.value.2 hs.2.1 old z.value.1 hs.1 M U
    change (numberFieldEncoding basis).encode
      ([totalEvaluation M U (fun _ => 1) (z.value.2.stretchLabelLength bt old.val z.value.1)].sum) = _
    rw [List.sum_cons, List.sum_nil, add_zero, totalEvaluation_valid _ _ _ _ hv, hc]
    have hd : DynamicMatrixFamilySource.queryEncoding.decode raw = some z.value :=
      BitEncoding.ValidWord.decode_raw z
    simp only [DynamicMatrixFamilySource.problem, encodedFunction, hd,
      DynamicMatrixFamilySource.answer]
    congr 1
    exact (totalEvaluation_valid (appendOne M (M old ^ z.value.1)) U (fun _ => 1) z.value.2 hs.2.1).symm
  · intro raw h
    obtain ⟨g, hd, hg⟩ := h
    change (evaluationValue basis M U (fun _ => 1) raw).length ≤ p.eval raw.length
    rw [evaluationValue_decode _ _ _ _ raw g hd hg.1]
    exact hbound raw g hg.1 hd

end PlanarHom.UniformMatrixPowerSimulation
