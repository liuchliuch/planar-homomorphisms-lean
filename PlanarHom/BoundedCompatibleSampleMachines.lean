import PlanarHom.MaterializedCollisionTestMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.ListContextFilterMachines

/-! Actual bounded search for a length-compatible sample of an FP field-vector family. -/
namespace PlanarHom.BoundedCompatibleSampleMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [DecidableEq K] {t : ℕ}

/-- Candidate count, current factor count, and the materialized target vector. -/
abbrev Input (K : Type) (t : ℕ) := ℕ × (ℕ × (Fin t → K))

/-- The cap makes this candidate test total even for an arbitrary binary index. -/
def accept (A : ℕ → Fin t → K) (p : Input K t × ℕ) : Bool :=
  MaterializedCollisionTestMachines.test (p.1.2.1, (A (min p.1.1 p.2), p.1.2.2))

/-- The actual range enumerator supplies descending indices below the unary count. -/
def candidates (A : ℕ → Fin t → K) (p : Input K t) : List ℕ :=
  (List.range p.1).reverse.filter (fun n => accept A (p, n))

/-- Total search, returning zero if no candidate passes. Existence is a semantic
premise of the correctness theorem, never a premise of the machine. -/
def search (A : ℕ → Fin t → K) (p : Input K t) : ℕ := (candidates A p).headD 0

theorem mem_candidates_iff (A : ℕ → Fin t → K) (p : Input K t) (n : ℕ) :
    n ∈ candidates A p ↔ n < p.1 ∧ ExponentProductTables.CompatibleAt (A n) p.2.2 p.2.1 := by
  simp only [candidates, List.mem_filter, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨hn, ha⟩
    have hc := (MaterializedCollisionTestMachines.test_eq_true_iff _).mp ha
    exact ⟨hn, by simpa only [min_eq_right (Nat.le_of_lt hn)] using hc⟩
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    apply (MaterializedCollisionTestMachines.test_eq_true_iff _).mpr
    simpa only [min_eq_right (Nat.le_of_lt hn)] using hc

/-- A compatible candidate in the explicit range forces the returned index to be
in that range and compatible at exactly the current input's factor count. -/
theorem search_spec (A : ℕ → Fin t → K) (p : Input K t)
    (hex : ∃ n < p.1, ExponentProductTables.CompatibleAt (A n) p.2.2 p.2.1) :
    search A p < p.1 ∧ ExponentProductTables.CompatibleAt (A (search A p)) p.2.2 p.2.1 := by
  obtain ⟨n, hn, hc⟩ := hex
  have hm := (mem_candidates_iff A p n).mpr ⟨hn, hc⟩
  have hs : search A p ∈ candidates A p := by
    cases hl : candidates A p with
    | nil => simp [hl] at hm
    | cons x xs => simp [search, hl]
  exact (mem_candidates_iff A p _).mp hs

/-- Failure of this finite test is exactly the absence of compatible candidates. -/
theorem candidates_eq_nil_iff (A : ℕ → Fin t → K) (p : Input K t) :
    candidates A p = [] ↔ ¬∃ n < p.1, ExponentProductTables.CompatibleAt (A n) p.2.2 p.2.1 := by
  constructor
  · intro h ⟨n, hn, hc⟩
    have hm := (mem_candidates_iff A p n).mpr ⟨hn, hc⟩
    simp [h] at hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n hn
    exact h ⟨n, (mem_candidates_iff A p n).mp hn⟩

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- Both varying counts are unary; every target coordinate is literally encoded. -/
noncomputable def inputEncoding (t : ℕ) : BitEncoding (Input K t) :=
  BitEncoding.unaryNat.prod (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t))

variable (A : ℕ → Fin t → K)

/-- The family evaluator is an explicit actual-FP premise, suitable for both
polynomial evaluation and unary-counted matrix-power families. -/
theorem fp_accept (hA : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t) A) : FP ((inputEncoding basis t).prod BitEncoding.nat) BitEncoding.bool (accept A) := by
  have hp := fp_fst (inputEncoding basis t) BitEncoding.nat
  have hn := fp_snd (inputEncoding basis t) BitEncoding.nat
  have hb := hp.comp (fp_fst BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t)))
  have ht := hp.comp (fp_snd BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t)))
  have hm := ht.comp (fp_fst BitEncoding.unaryNat ((numberFieldEncoding basis).vector t))
  have htarget := ht.comp (fp_snd BitEncoding.unaryNat ((numberFieldEncoding basis).vector t))
  have hi := (hb.pair hn).comp ⟨BoundedUnaryMachines.computer⟩
  have hs := hi.comp hA
  exact (hm.pair (hs.pair htarget)).comp (MaterializedCollisionTestMachines.fp_test basis)

theorem fp_candidates (hA : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t) A) : FP (inputEncoding basis t) BitEncoding.nat.list (candidates A) := by
  have hb := fp_fst BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t))
  have hr := hb.comp UnaryRangeMachines.fp_range
  exact ((fp_id (inputEncoding basis t)).pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext (inputEncoding basis t) BitEncoding.nat
      (accept A) (fp_accept basis A hA))

/-- Actual range/filter/head bounded search, charged to the two unary counts
and all materialized target bits. No sample-existence or separation oracle. -/
theorem fp_search (hA : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t) A) : FP (inputEncoding basis t) BitEncoding.nat (search A) :=
  (fp_candidates basis A hA).comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)

/-- The selected source vector is actually evaluated at the returned index. -/
def selectedSource (A : ℕ → Fin t → K) (p : Input K t) : Fin t → K :=
  A (min p.1 (search A p))

theorem fp_selectedSource (hA : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector t) A) : FP (inputEncoding basis t) ((numberFieldEncoding basis).vector t)
    (selectedSource A) := by
  have hb := fp_fst BitEncoding.unaryNat
    (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t))
  exact (((hb.pair (fp_search basis A hA)).comp ⟨BoundedUnaryMachines.computer⟩).comp hA)

omit [Algebra ℚ K] in
theorem selectedSource_spec (A : ℕ → Fin t → K) (p : Input K t)
    (hex : ∃ n < p.1, ExponentProductTables.CompatibleAt (A n) p.2.2 p.2.1) :
    selectedSource A p = A (search A p) ∧
      ExponentProductTables.CompatibleAt (selectedSource A p) p.2.2 p.2.1 := by
  obtain ⟨hn, hc⟩ := search_spec A p hex
  simp only [selectedSource, min_eq_right (Nat.le_of_lt hn)]
  exact ⟨trivial, hc⟩

end PlanarHom.BoundedCompatibleSampleMachines
