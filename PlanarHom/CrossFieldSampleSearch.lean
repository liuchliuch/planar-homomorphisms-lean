import PlanarHom.CrossFieldCollisionMachines
import PlanarHom.BoundedCompatibleSampleMachines

/-! Exact range/filter/head search for current-length heterogeneous-field compatibility. -/
noncomputable section
namespace PlanarHom.CrossFieldSampleSearch
open Complexity PairProjectionMachines
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
variable {t : ℕ} (A : ℕ → Fin t → L) (B : ∀ x, Fin t → K x)

abbrev Input (X : Type) := ℕ × (X × ℕ)

def accept (p : Input X × ℕ) : Bool :=
  CrossFieldCollisionMachines.test K B (p.1.2,A (min p.1.1 p.2))
def candidates (p : Input X) : List ℕ :=
  (List.range p.1).reverse.filter (fun n => accept K A B (p,n))
def search (p : Input X) : ℕ := (candidates K A B p).headD 0

theorem mem_candidates_iff (p : Input X) (n : ℕ) : n ∈ candidates K A B p ↔
    n < p.1 ∧ SourceExponentRepresentatives.CrossCompatibleAt (A n) (B p.2.1) p.2.2 := by
  simp only [candidates, List.mem_filter, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨hn,ha⟩
    have hc := (CrossFieldCollisionMachines.test_eq_true_iff K B _).mp ha
    exact ⟨hn,by simpa only [min_eq_right (Nat.le_of_lt hn)] using hc⟩
  · rintro ⟨hn,hc⟩
    refine ⟨hn,?_⟩
    apply (CrossFieldCollisionMachines.test_eq_true_iff K B _).mpr
    simpa only [min_eq_right (Nat.le_of_lt hn)] using hc

theorem search_spec (p : Input X)
    (hex : ∃ n < p.1, SourceExponentRepresentatives.CrossCompatibleAt (A n) (B p.2.1) p.2.2) :
    search K A B p < p.1 ∧
      SourceExponentRepresentatives.CrossCompatibleAt (A (search K A B p)) (B p.2.1) p.2.2 := by
  obtain ⟨n,hn,hc⟩ := hex
  have hm := (mem_candidates_iff K A B p n).mpr ⟨hn,hc⟩
  have hs : search K A B p ∈ candidates K A B p := by
    cases hl : candidates K A B p with
    | nil => simp [hl] at hm
    | cons x xs => simp [search,hl]
  exact (mem_candidates_iff K A B p _).mp hs

variable {sourceDimension : ℕ} (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
def inputEncoding : BitEncoding (Input X) := BitEncoding.unaryNat.prod (ex.prod BitEncoding.unaryNat)

variable (hA : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector t) A)
variable (htest : FP ((ex.prod BitEncoding.unaryNat).prod ((numberFieldEncoding sourceBasis).vector t))
  BitEncoding.bool (CrossFieldCollisionMachines.test K B))

include hA htest in
theorem fp_accept : FP ((inputEncoding ex).prod BitEncoding.nat) BitEncoding.bool (accept K A B) := by
  have hp := fp_fst (inputEncoding ex) BitEncoding.nat
  have hn := fp_snd (inputEncoding ex) BitEncoding.nat
  have hc := hp.comp (fp_fst BitEncoding.unaryNat (ex.prod BitEncoding.unaryNat))
  have hx := hp.comp (fp_snd BitEncoding.unaryNat (ex.prod BitEncoding.unaryNat))
  have hs := ((hc.pair hn).comp ⟨BoundedUnaryMachines.computer⟩).comp hA
  exact (hx.pair hs).comp htest

include hA htest in
theorem fp_candidates : FP (inputEncoding ex) BitEncoding.nat.list (candidates K A B) := by
  have hc := fp_fst BitEncoding.unaryNat (ex.prod BitEncoding.unaryNat)
  have hr := hc.comp UnaryRangeMachines.fp_range
  exact ((fp_id (inputEncoding ex)).pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext (inputEncoding ex) BitEncoding.nat _
      (fp_accept K A B sourceBasis ex hA htest))

include hA htest in
theorem fp_search : FP (inputEncoding ex) BitEncoding.nat (search K A B) :=
  (fp_candidates K A B sourceBasis ex hA htest).comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)

end PlanarHom.CrossFieldSampleSearch
