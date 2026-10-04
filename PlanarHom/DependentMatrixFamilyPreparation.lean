import PlanarHom.CrossFieldSampleSearch
import PlanarHom.DynamicMatrixFamilyPreparation

/-! Actual variable-field sample selection, source-only exponent tables, and original-codec query batches. -/
noncomputable section
namespace PlanarHom.DependentMatrixFamilyPreparation
open Complexity Complexity.MixedCode PairProjectionMachines
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
variable {q : ℕ} (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x))
variable (n₀ : ℕ) (candidates : Polynomial ℕ) (selected : ℕ)

def searchInput (p : X × MixedCode) : CrossFieldSampleSearch.Input X :=
  (candidates.eval (p.2.markedCount selected),(p.1,p.2.markedCount selected))
def sampleIndex (p : X × MixedCode) : ℕ :=
  let s := searchInput candidates selected p
  n₀ + min s.1 (CrossFieldSampleSearch.search K (DynamicMatrixFamilyPreparation.family F n₀)
    (fun x => binaryAlphabet (B x)) s)
def table (p : X × MixedCode) : List (L × List ℕ) :=
  SourceExponentRepresentatives.representatives (binaryAlphabet (F (sampleIndex K F B n₀ candidates selected p)))
    (p.2.markedCount selected)
def preparation (p : X × MixedCode) : ((X × ℕ) × List (L × List ℕ)) × List (ℕ × MixedCode) :=
  (((p.1,p.2.markedCount selected),table K F B n₀ candidates selected p),
    (GraphInterpolationQueries.queries (MixedCode.parallelLabel selected)
      ((table K F B n₀ candidates selected p).length,p.2)).map
        (fun g => (sampleIndex K F B n₀ candidates selected p,g)))

theorem sample_spec (p : X × MixedCode)
    (hex : ∃ j < candidates.eval (p.2.markedCount selected),
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B p.1))
        (p.2.markedCount selected)) :
    n₀ ≤ sampleIndex K F B n₀ candidates selected p ∧
      sampleIndex K F B n₀ candidates selected p < n₀ + candidates.eval (p.2.markedCount selected) ∧
      SourceExponentRepresentatives.CrossCompatibleAt
        (binaryAlphabet (F (sampleIndex K F B n₀ candidates selected p))) (binaryAlphabet (B p.1))
        (p.2.markedCount selected) := by
  have h := CrossFieldSampleSearch.search_spec K (DynamicMatrixFamilyPreparation.family F n₀)
    (fun x => binaryAlphabet (B x)) (searchInput candidates selected p) hex
  dsimp only [searchInput] at h
  dsimp only [sampleIndex,searchInput]
  rw [min_eq_right (Nat.le_of_lt h.1)]
  exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left h.1 _,h.2⟩

theorem query_mem {p : X × MixedCode} {query : ℕ × MixedCode}
    (hquery : query ∈ (preparation K F B n₀ candidates selected p).2) :
    ∃ h, 1 ≤ h ∧ h ≤ (table K F B n₀ candidates selected p).length ∧
      query = (sampleIndex K F B n₀ candidates selected p,p.2.parallelLabel selected h) := by
  obtain ⟨inner,hinner,rfl⟩ := List.mem_map.mp hquery
  obtain ⟨h,hh,hb,rfl⟩ := GraphInterpolationQueries.mem_queries hinner
  exact ⟨h,hh,hb,rfl⟩

variable {sourceDimension : ℕ} (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
def contextEncoding := (ex.prod BitEncoding.unaryNat).prod (SourceExponentRepresentatives.rowEncoding sourceBasis).list

variable (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
  (fun n => binaryAlphabet (F n)))
variable (htest : FP ((ex.prod BitEncoding.unaryNat).prod ((numberFieldEncoding sourceBasis).vector (q*q)))
  BitEncoding.bool (CrossFieldCollisionMachines.test K (fun x => binaryAlphabet (B x))))

theorem fp_searchInput : FP (ex.prod MixedCode.encoding) (CrossFieldSampleSearch.inputEncoding ex)
    (searchInput candidates selected) := by
  have hx := fp_fst ex MixedCode.encoding
  have hm := (fp_snd ex MixedCode.encoding).comp (MixedCode.fp_unaryMarkedCount selected)
  exact (hm.comp (UnaryPolynomialMachines.fp_eval candidates)).pair (hx.pair hm)

include hF htest in
theorem fp_sampleIndex : FP (ex.prod MixedCode.encoding) BitEncoding.unaryNat
    (sampleIndex K F B n₀ candidates selected) := by
  have hp := fp_searchInput candidates selected ex
  have hb := hp.comp (fp_fst BitEncoding.unaryNat (ex.prod BitEncoding.unaryNat))
  have hf : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (DynamicMatrixFamilyPreparation.family F n₀) := (UnaryPolynomialMachines.fp_offset n₀).comp hF
  have hn := hp.comp (CrossFieldSampleSearch.fp_search K (DynamicMatrixFamilyPreparation.family F n₀)
    (fun x => binaryAlphabet (B x)) sourceBasis ex hf htest)
  exact (((hb.pair hn).comp ⟨BoundedUnaryMachines.computer⟩).comp (UnaryPolynomialMachines.fp_offset n₀))

include hF htest in
theorem fp_table : FP (ex.prod MixedCode.encoding) (SourceExponentRepresentatives.rowEncoding sourceBasis).list
    (table K F B n₀ candidates selected) := by
  have hm := (fp_snd ex MixedCode.encoding).comp (MixedCode.fp_unaryMarkedCount selected)
  have ha := (fp_sampleIndex K F B n₀ candidates selected sourceBasis ex hF htest).comp hF
  exact (hm.pair ha).comp (SourceExponentRepresentatives.fp_representatives sourceBasis)

include hF htest in
theorem fp_preparation : FP (ex.prod MixedCode.encoding)
    ((contextEncoding sourceBasis ex).prod DynamicMatrixFamilySource.queryEncoding.list)
    (preparation K F B n₀ candidates selected) := by
  have hx := fp_fst ex MixedCode.encoding
  have hg := fp_snd ex MixedCode.encoding
  have hm := hg.comp (MixedCode.fp_unaryMarkedCount selected)
  have ht := fp_table K F B n₀ candidates selected sourceBasis ex hF htest
  have hn := fp_sampleIndex K F B n₀ candidates selected sourceBasis ex hF htest
  have hl := ht.comp (ListUnaryLengthMachine.fp_length (SourceExponentRepresentatives.rowEncoding sourceBasis))
  have hq := (hl.pair hg).comp (GraphInterpolationQueries.fp_binaryQueries selected)
  have htag := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat MixedCode.encoding
    DynamicMatrixFamilySource.queryEncoding (fun p : ℕ × MixedCode => p) (fp_id DynamicMatrixFamilySource.queryEncoding)
  exact ((hx.pair hm).pair ht).pair ((hn.pair hq).comp htag)

end PlanarHom.DependentMatrixFamilyPreparation
