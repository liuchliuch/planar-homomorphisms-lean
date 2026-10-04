import PlanarHom.DynamicMatrixFamilyPreparation

/-! Uniform preprocessing for an exactly encoded runtime target parameter in one fixed field. -/
namespace PlanarHom.ParameterizedMatrixFamilyPreparation
open Complexity Complexity.MixedCode ArithmeticCircuitPrimitives PairProjectionMachines
variable {X K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension q : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
variable (F : ℕ → Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K)
variable (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ)

noncomputable def preparation (p : X × MixedCode) : List (K × K) × List (ℕ × MixedCode) :=
  DynamicMatrixFamilyPreparation.preparation F (B p.1) n₀ c selected p.2

omit [DecidableEq K] in
theorem fp_searchInput
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x))) :
    FP (ex.prod MixedCode.encoding) (BoundedCompatibleSampleMachines.inputEncoding basis (q*q))
      (fun p => DynamicMatrixFamilyPreparation.searchInput (B p.1) c selected p.2) := by
  have hx := fp_fst ex MixedCode.encoding
  have hg := fp_snd ex MixedCode.encoding
  have hm := hg.comp (MixedCode.fp_unaryMarkedCount selected)
  have hb := hx.comp hB
  exact ((hm.comp (UnaryPolynomialMachines.fp_eval c)).pair (hm.pair hb))

theorem fp_sampleIndex
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x))) :
    FP (ex.prod MixedCode.encoding) BitEncoding.unaryNat
      (fun p => DynamicMatrixFamilyPreparation.sampleIndex F (B p.1) n₀ c selected p.2) := by
  have hp := fp_searchInput basis ex B c selected hB
  have hb := hp.comp (fp_fst BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector (q*q))))
  have hf : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (DynamicMatrixFamilyPreparation.family F n₀) := (UnaryPolynomialMachines.fp_offset n₀).comp hF
  have hn := hp.comp (BoundedCompatibleSampleMachines.fp_search basis (DynamicMatrixFamilyPreparation.family F n₀) hf)
  exact (((hb.pair hn).comp ⟨BoundedUnaryMachines.computer⟩).comp (UnaryPolynomialMachines.fp_offset n₀))

theorem fp_table
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x))) :
    FP (ex.prod MixedCode.encoding) (DynamicMatrixFamilyPreparation.tableEncoding basis)
      (fun p => DynamicMatrixFamilyPreparation.table F (B p.1) n₀ c selected p.2) := by
  have hx := fp_fst ex MixedCode.encoding
  have hg := fp_snd ex MixedCode.encoding
  have hm := hg.comp (MixedCode.fp_unaryMarkedCount selected)
  have ha := (fp_sampleIndex basis ex F B n₀ c selected hF hB).comp hF
  exact (hm.pair (ha.pair (hx.comp hB))).comp (MaterializedProductTableMachines.fp_representatives basis)

/-- The actual parameter evaluator runs on its literal input word; c depends only
on marked length, and source evaluation uses the original fixed family F. -/
theorem fp_preparation
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x))) :
    FP (ex.prod MixedCode.encoding)
      ((DynamicMatrixFamilyPreparation.tableEncoding basis).prod DynamicMatrixFamilySource.queryEncoding.list)
      (preparation F B n₀ c selected) := by
  have ht := fp_table basis ex F B n₀ c selected hF hB
  have hn := fp_sampleIndex basis ex F B n₀ c selected hF hB
  have hg := fp_snd ex MixedCode.encoding
  have hl := ht.comp (ListUnaryLengthMachine.fp_length ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
  have hq := (hl.pair hg).comp (GraphInterpolationQueries.fp_binaryQueries selected)
  have htag := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat MixedCode.encoding
    DynamicMatrixFamilySource.queryEncoding (fun p : ℕ × MixedCode => p) (fp_id DynamicMatrixFamilySource.queryEncoding)
  exact ht.pair ((hn.pair hq).comp htag)

end PlanarHom.ParameterizedMatrixFamilyPreparation
