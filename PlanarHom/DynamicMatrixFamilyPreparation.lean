import PlanarHom.BoundedCompatibleSampleMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.DynamicMatrixFamilySource
import PlanarHom.GraphInterpolationQueries

/-! Actual selected-sample tables and tagged parallel-query batches for Lemma 3.10. -/
namespace PlanarHom.DynamicMatrixFamilyPreparation
open Complexity Complexity.MixedCode ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [DecidableEq K] {q : ℕ}

/-- Shift the family before bounded candidate search; the true source index is
restored in every submitted query. -/
noncomputable def family (F : ℕ → Matrix (Fin q) (Fin q) K) (n₀ : ℕ) : ℕ → Fin (q*q) → K :=
  fun j => binaryAlphabet (F (n₀+j))

noncomputable def searchInput (B : Matrix (Fin q) (Fin q) K) (c : Polynomial ℕ)
    (selected : ℕ) (g : MixedCode) : BoundedCompatibleSampleMachines.Input K (q*q) :=
  let m := g.markedCount selected
  (c.eval m, (m, binaryAlphabet B))

noncomputable def sampleIndex (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ) (g : MixedCode) : ℕ :=
  let p := searchInput B c selected g
  n₀ + min p.1 (BoundedCompatibleSampleMachines.search (family F n₀) p)

noncomputable def table (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ) (g : MixedCode) : List (K × K) :=
  ExponentProductTables.representatives (binaryAlphabet (F (sampleIndex F B n₀ c selected g)))
    (binaryAlphabet B) (g.markedCount selected)

noncomputable def preparation (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ) (g : MixedCode) : List (K × K) × List (ℕ × MixedCode) :=
  (table F B n₀ c selected g,
    (GraphInterpolationQueries.queries (MixedCode.parallelLabel selected)
      ((table F B n₀ c selected g).length, g)).map (fun query => (sampleIndex F B n₀ c selected g, query)))

/-- The search theorem supplies compatibility at the current marked length,
including the empty-product case m=0. -/
theorem sample_spec (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ) (g : MixedCode)
    (hex : ∃ j < c.eval (g.markedCount selected),
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B)
        (g.markedCount selected)) :
    n₀ ≤ sampleIndex F B n₀ c selected g ∧
      sampleIndex F B n₀ c selected g < n₀ + c.eval (g.markedCount selected) ∧
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (sampleIndex F B n₀ c selected g)))
        (binaryAlphabet B) (g.markedCount selected) := by
  have h := BoundedCompatibleSampleMachines.search_spec (family F n₀) (searchInput B c selected g) hex
  dsimp only [searchInput] at h
  dsimp only [sampleIndex, searchInput]
  rw [min_eq_right (Nat.le_of_lt h.1)]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left h.1 _, h.2⟩

/-- Every query preserves its selected source sample and uses a positive
parallel multiplicity bounded by the actual retained table length. -/
theorem query_mem {F : ℕ → Matrix (Fin q) (Fin q) K} {B : Matrix (Fin q) (Fin q) K}
    {n₀ : ℕ} {c : Polynomial ℕ} {selected : ℕ} {g : MixedCode} {query : ℕ × MixedCode}
    (hquery : query ∈ (preparation F B n₀ c selected g).2) :
    ∃ h, 1 ≤ h ∧ h ≤ (table F B n₀ c selected g).length ∧
      query = (sampleIndex F B n₀ c selected g, g.parallelLabel selected h) := by
  change query ∈ (GraphInterpolationQueries.queries (MixedCode.parallelLabel selected)
    ((table F B n₀ c selected g).length, g)).map (fun inner => (sampleIndex F B n₀ c selected g, inner)) at hquery
  obtain ⟨inner, hinner, rfl⟩ := List.mem_map.mp hquery
  obtain ⟨h, hh, hb, rfl⟩ := GraphInterpolationQueries.mem_queries hinner
  exact ⟨h, hh, hb, rfl⟩

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
variable (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
variable (n₀ : ℕ) (c : Polynomial ℕ) (selected : ℕ)

noncomputable def tableEncoding := ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list

omit [DecidableEq K] in
theorem fp_searchInput : FP MixedCode.encoding (BoundedCompatibleSampleMachines.inputEncoding basis (q*q))
    (searchInput B c selected) :=
  (((MixedCode.fp_unaryMarkedCount selected).comp (UnaryPolynomialMachines.fp_eval c)).pair
    ((MixedCode.fp_unaryMarkedCount selected).pair
      (fp_const MixedCode.encoding ((numberFieldEncoding basis).vector (q*q)) (binaryAlphabet B))))

theorem fp_sampleIndex
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n))) :
    FP MixedCode.encoding BitEncoding.unaryNat (sampleIndex F B n₀ c selected) := by
  have hp := fp_searchInput basis B c selected
  have hb := hp.comp (fp_fst BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector (q*q))))
  have hf : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (family F n₀) :=
    (UnaryPolynomialMachines.fp_offset n₀).comp hF
  have hn := hp.comp (BoundedCompatibleSampleMachines.fp_search basis (family F n₀) hf)
  exact (((hb.pair hn).comp ⟨BoundedUnaryMachines.computer⟩).comp (UnaryPolynomialMachines.fp_offset n₀))

theorem fp_table
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n))) :
    FP MixedCode.encoding (tableEncoding basis) (table F B n₀ c selected) := by
  have hm := MixedCode.fp_unaryMarkedCount selected
  have ha := (fp_sampleIndex basis F B n₀ c selected hF).comp hF
  have hb := fp_const MixedCode.encoding ((numberFieldEncoding basis).vector (q*q)) (binaryAlphabet B)
  exact (hm.pair (ha.pair hb)).comp (MaterializedProductTableMachines.fp_representatives basis)

theorem fp_preparation
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q)) (fun n => binaryAlphabet (F n))) :
    FP MixedCode.encoding ((tableEncoding basis).prod DynamicMatrixFamilySource.queryEncoding.list)
      (preparation F B n₀ c selected) := by
  have ht := fp_table basis F B n₀ c selected hF
  have hn := fp_sampleIndex basis F B n₀ c selected hF
  have hl := ht.comp (ListUnaryLengthMachine.fp_length ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
  have hq := (hl.pair (fp_id MixedCode.encoding)).comp (GraphInterpolationQueries.fp_binaryQueries selected)
  have htag := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat MixedCode.encoding
    DynamicMatrixFamilySource.queryEncoding (fun p : ℕ × MixedCode => p) (fp_id DynamicMatrixFamilySource.queryEncoding)
  exact ht.pair ((hn.pair hq).comp htag)

end PlanarHom.DynamicMatrixFamilyPreparation
