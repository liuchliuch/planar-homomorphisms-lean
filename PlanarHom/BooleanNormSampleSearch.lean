import PlanarHom.ExponentVectorMachines
import PlanarHom.ListContextFilterMachines
import PlanarHom.ListPredicateMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.BooleanExceptionalGrid

/-! An actual finite rational-grid search over all bounded count-vector pairs. -/
noncomputable section
namespace PlanarHom.BooleanNormSampleSearch
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines

/-- Grid length, unary exponent cap, and the actual count list. -/
abbrev Input := ℕ × (ℕ × List ℕ)
abbrev CountPair := List ℕ × List ℕ
abbrev Row := (Input × ℚ) × CountPair

def inputEncoding : BitEncoding Input :=
  BitEncoding.unaryNat.prod (BitEncoding.unaryNat.prod BitEncoding.nat.list)
def pairEncoding : BitEncoding CountPair := BitEncoding.nat.list.prod BitEncoding.nat.list
def rowEncoding : BitEncoding Row := (inputEncoding.prod BitEncoding.rat).prod pairEncoding

def pairs (b : ℕ) (p : Input) : List CountPair :=
  (ExponentVectors.box b p.2.1).flatMap fun k =>
    (ExponentVectors.box b p.2.1).map fun l => (k,l)

theorem mem_pairs_iff (b : ℕ) (p : Input) (kl : CountPair) :
    kl ∈ pairs b p ↔ kl.1 ∈ ExponentVectors.box b p.2.1 ∧
      kl.2 ∈ ExponentVectors.box b p.2.1 := by
  rcases kl with ⟨k,l⟩
  simp [pairs]

theorem length_pairs (b : ℕ) (p : Input) :
    (pairs b p).length = (p.2.1+1)^b * (p.2.1+1)^b := by
  simp [pairs, List.length_flatMap, ExponentVectors.length_box]

theorem fp_pairs (b : ℕ) : FP inputEncoding pairEncoding.list (pairs b) := by
  let e := BitEncoding.nat.list
  have hi := ListContextMachines.fp_mapWithContext e e (e.prod e) id (fp_id (e.prod e))
  have hs := ((fp_snd e.list e).pair (fp_fst e.list e)).comp hi
  have hm := ListContextMachines.fp_mapWithContext e.list e (e.prod e).list
    (fun p : List (List ℕ) × List ℕ => p.1.map (fun l => (p.2,l))) hs
  have hc := (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod e)).comp
    (fp_fst BitEncoding.unaryNat e)
  have hb := hc.comp (ExponentVectorMachines.fp_box b)
  exact (((hb.pair hb).comp hm).comp (ListFlattenMachines.fp_flatten (e.prod e))).congr
    (fun p => by simp only [Function.comp_apply, pairs, List.flatMap])

def grid (N : ℕ) : List ℚ :=
  (List.range N).reverse.map (fun j => BooleanExceptionalGrid.rationalSample N (j+1))

theorem fp_grid : FP BitEncoding.unaryNat BitEncoding.rat.list grid := by
  have hN := (fp_fst BitEncoding.unaryNat BitEncoding.nat).comp
    UnaryNatConversionMachine.fp_conversion
  have hj := fp_snd BitEncoding.unaryNat BitEncoding.nat
  have hn := ((hj.comp BinaryArithmetic.fp_successor).comp fp_nat_int).comp fp_int_rat
  have hd := ((hN.comp BinaryArithmetic.fp_successor).comp fp_nat_int).comp fp_int_rat
  have hq := (hn.pair hd).comp RationalCircuits.fp_rational_division
  exact (((fp_id BitEncoding.unaryNat).pair UnaryRangeMachines.fp_range).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat BitEncoding.nat BitEncoding.rat
      (fun p => BooleanExceptionalGrid.rationalSample p.1 (p.2+1)) hq)).congr (fun _ => rfl)

theorem mem_grid_iff (N : ℕ) (q : ℚ) :
    q ∈ grid N ↔ q ∈ BooleanExceptionalGrid.rationalGrid N := by
  rw [BooleanExceptionalGrid.mem_rationalGrid_iff]
  simp only [grid, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j+1,by omega,by omega,rfl⟩
  · rintro ⟨j,hj,hjN,rfl⟩
    refine ⟨j-1,by omega,?_⟩
    simp only [BooleanExceptionalGrid.rationalSample, Nat.sub_add_cancel hj]

theorem nodup_grid (N : ℕ) : (grid N).Nodup := by
  apply List.Nodup.map
  · intro i j h
    exact Nat.add_right_cancel (BooleanExceptionalGrid.rationalSample_injective N h)
  · simpa only [List.nodup_reverse] using (List.nodup_range (n := N))

/-- Every actual count-vector pair is tested at the same exact rational sample. -/
def accept (b : ℕ) (bad : Row → Bool) (p : Input × ℚ) : Bool :=
  !((pairs b p.1).any (fun kl => bad (p,kl)))

def candidates (b : ℕ) (bad : Row → Bool) (p : Input) : List ℚ :=
  (grid p.1).filter (fun q => accept b bad (p,q))

def search (b : ℕ) (bad : Row → Bool) (p : Input) : ℚ :=
  (candidates b bad p).headD 0

theorem accept_eq_true_iff (b : ℕ) (bad : Row → Bool) (p : Input × ℚ) :
    accept b bad p = true ↔ ∀ kl ∈ pairs b p.1, bad (p,kl) = false := by
  simp [accept, List.any_eq_false]

theorem mem_candidates_iff (b : ℕ) (bad : Row → Bool) (p : Input) (q : ℚ) :
    q ∈ candidates b bad p ↔ q ∈ BooleanExceptionalGrid.rationalGrid p.1 ∧
      ∀ kl ∈ pairs b p, bad ((p,q),kl) = false := by
  simp only [candidates, List.mem_filter, mem_grid_iff, accept_eq_true_iff]

theorem nodup_candidates (b : ℕ) (bad : Row → Bool) (p : Input) :
    (candidates b bad p).Nodup := (nodup_grid p.1).filter _

theorem fp_accept (b : ℕ) (bad : Row → Bool) (hbad : FP rowEncoding BitEncoding.bool bad) :
    FP (inputEncoding.prod BitEncoding.rat) BitEncoding.bool (accept b bad) := by
  let ec := inputEncoding.prod BitEncoding.rat
  have hp := (fp_fst inputEncoding BitEncoding.rat).comp (fp_pairs b)
  have hm := ListContextMachines.fp_mapWithContext ec pairEncoding BitEncoding.bool bad hbad
  have ha := (((fp_id ec).pair hp).comp hm).comp
    (ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))
  exact (ha.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr
    (fun p => by simp [accept, List.any_map])

theorem fp_candidates (b : ℕ) (bad : Row → Bool) (hbad : FP rowEncoding BitEncoding.bool bad) :
    FP inputEncoding BitEncoding.rat.list (candidates b bad) := by
  have hg := (fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)).comp fp_grid
  exact ((fp_id inputEncoding).pair hg).comp
    (ListContextFilterMachines.fp_filterWithContext inputEncoding BitEncoding.rat
      (accept b bad) (fp_accept b bad hbad))

theorem fp_search (b : ℕ) (bad : Row → Bool) (hbad : FP rowEncoding BitEncoding.bool bad) :
    FP inputEncoding BitEncoding.rat (search b bad) :=
  (fp_candidates b bad hbad).comp (ListDecompositionMachines.fp_headD BitEncoding.rat 0)

/-- Correctness of the literal first retained sample; existence is used only for
correctness, never by the finite machine compiler. -/
theorem search_spec (b : ℕ) (bad : Row → Bool) (p : Input)
    (hex : ∃ q ∈ BooleanExceptionalGrid.rationalGrid p.1,
      ∀ kl ∈ pairs b p, bad ((p,q),kl) = false) :
    search b bad p ∈ BooleanExceptionalGrid.rationalGrid p.1 ∧
      ∀ kl ∈ pairs b p, bad ((p,search b bad p),kl) = false := by
  obtain ⟨q,hq,hgood⟩ := hex
  have hmem := (mem_candidates_iff b bad p q).mpr ⟨hq,hgood⟩
  apply (mem_candidates_iff b bad p _).mp
  cases hl : candidates b bad p with
  | nil => simp [hl] at hmem
  | cons x xs => simp [search,hl]

end PlanarHom.BooleanNormSampleSearch
