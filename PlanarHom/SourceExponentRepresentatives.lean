import PlanarHom.MaterializedProductTableMachines
import PlanarHom.ExponentProductSemantics

/-! Stable source-key tables retain the original exponent lists for evaluation in another field. -/
namespace PlanarHom.SourceExponentRepresentatives
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines ListDedupMachines
open scoped BigOperators
variable {K : Type} [Field K] {t : ℕ}

def products (A : Fin t → K) (m : ℕ) : List (K × List ℕ) :=
  (ExponentVectors.weak t m).map (fun xs => (ExponentProductSemantics.value A xs, xs))

variable [DecidableEq K]

def nonzeroProducts (A : Fin t → K) (m : ℕ) : List (K × List ℕ) :=
  (products A m).filter (fun row => decide (row.1 ≠ 0))

def representatives (A : Fin t → K) (m : ℕ) : List (K × List ℕ) :=
  dedupByFirst (fun p : K × K => decide (p.1 = p.2)) (nonzeroProducts A m)

omit [DecidableEq K] in
theorem products_vectors (A : Fin t → K) (m : ℕ) :
    products A m = (ExponentProductTables.vectors t m).map
      (fun r => (∏ i, A i ^ r i, List.ofFn r)) := by
  have he := ExponentProductTables.vectors_encoding t m
  have hl : (ExponentProductTables.vectors t m).map List.ofFn = ExponentVectors.weak t m := by
    apply BitEncoding.nat.list.list.injective
    simpa only [BitEncoding.list, List.length_map, List.map_map, BitEncoding.vector,
      Function.comp_def] using he
  rw [products, ← hl, List.map_map]
  congr 1
  funext r
  simp [ExponentProductSemantics.value, List.getD_eq_getElem]

theorem representatives_sublist (A : Fin t → K) (m : ℕ) :
    (representatives A m).Sublist (products A m) :=
  (dedupByFirst_sublist _ _).trans List.filter_sublist

theorem mem_representatives (A : Fin t → K) (m : ℕ) (row : K × List ℕ)
    (hrow : row ∈ representatives A m) :
    row.2 ∈ ExponentVectors.weak t m ∧ row.1 = ExponentProductSemantics.value A row.2 ∧ row.1 ≠ 0 := by
  have hr := (dedupByFirst_sublist (fun p : K × K => decide (p.1 = p.2)) (nonzeroProducts A m)).subset hrow
  obtain ⟨hp,hz⟩ := List.mem_filter.mp hr
  obtain ⟨xs,hxs,he⟩ := List.mem_map.mp hp
  subst row
  exact ⟨hxs,rfl,of_decide_eq_true hz⟩

theorem length_representatives (A : Fin t → K) (m : ℕ) :
    (representatives A m).length ≤ (m+1)^t :=
  (representatives_sublist A m).length_le.trans (by simpa [products] using ExponentVectors.length_weak_le t m)

private theorem key_equivalence : Equivalence (Rel (fun p : K × K => decide (p.1 = p.2))) := by
  exact ⟨fun _ => by simp [ListDedupMachines.Rel], fun h => by simpa [ListDedupMachines.Rel, eq_comm] using h,
    fun h₁ h₂ => by simpa only [ListDedupMachines.Rel, decide_eq_true_eq] using Eq.trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)⟩

theorem representatives_pairwise (A : Fin t → K) (m : ℕ) :
    (representatives A m).Pairwise (fun a b => a.1 ≠ b.1) := by
  simpa only [ListDedupMachines.Rel, decide_eq_true_eq] using dedupByFirst_pairwise
    (fun p : K × K => decide (p.1 = p.2)) key_equivalence (nonzeroProducts A m)

theorem representatives_coverage (A : Fin t → K) (m : ℕ) (xs : List ℕ)
    (hxs : xs ∈ ExponentVectors.weak t m) (hz : ExponentProductSemantics.value A xs ≠ 0) :
    ∃ row ∈ representatives A m, row.1 = ExponentProductSemantics.value A xs := by
  have hmem : (ExponentProductSemantics.value A xs, xs) ∈ nonzeroProducts A m := by
    simp only [nonzeroProducts, List.mem_filter, decide_eq_true_eq]
    exact ⟨List.mem_map.mpr ⟨xs,hxs,rfl⟩,hz⟩
  obtain ⟨row,hr,he⟩ := dedupByFirst_coverage (fun p : K × K => decide (p.1 = p.2))
    key_equivalence (nonzeroProducts A m) _ hmem
  exact ⟨row,hr,(of_decide_eq_true he).symm⟩

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def inputEncoding (t : ℕ) := BitEncoding.unaryNat.prod ((numberFieldEncoding basis).vector t)
noncomputable def rowEncoding := (numberFieldEncoding basis).prod BitEncoding.nat.list

omit [DecidableEq K] in
theorem fp_products : FP (inputEncoding basis t) (rowEncoding basis).list
    (fun p : ℕ × (Fin t → K) => products p.2 p.1) := by
  let e := numberFieldEncoding basis
  let ei := inputEncoding basis t
  have hc := fp_fst ei (BitEncoding.nat.vector t)
  have hr := fp_snd ei (BitEncoding.nat.vector t)
  have hm := hc.comp (fp_fst BitEncoding.unaryNat (e.vector t))
  have ha := hc.comp (fp_snd BitEncoding.unaryNat (e.vector t))
  have hv := (hm.pair (ha.pair hr)).comp (MaterializedExponentProductMachines.fp_product basis)
  have hs : FP (ei.prod (BitEncoding.nat.vector t)) BitEncoding.nat.list
      (fun p => List.ofFn p.2) := hr.transportOutput (fun _ => rfl)
  have hmap := ListContextMachines.fp_mapWithContext ei (BitEncoding.nat.vector t)
    (rowEncoding basis) _ (hv.pair hs)
  have h := ((fp_id ei).pair ((fp_fst BitEncoding.unaryNat (e.vector t)).comp
    (ExponentProductTables.fp_vectors t))).comp hmap
  apply h.congr
  intro p
  rw [products_vectors]
  apply List.map_congr_left
  intro r hr
  congr 1
  exact MaterializedExponentProductMachines.product_eq p.1 p.2 r (ExponentProductTables.coordinate_le hr)

theorem fp_representatives : FP (inputEncoding basis t) (rowEncoding basis).list
    (fun p : ℕ × (Fin t → K) => representatives p.2 p.1) := by
  let e := numberFieldEncoding basis
  have heq := ((fp_fst e BitEncoding.nat.list).pair (fp_const (rowEncoding basis) e (0 : K))).comp
    (FixedFieldArithmetic.fp_equality basis)
  have hn : FP (rowEncoding basis) BitEncoding.bool (fun p : K × List ℕ => decide (p.1 ≠ 0)) :=
    (heq.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun _ => by simp)
  exact ((fp_products basis).comp (ListFilterMachines.fp_filter (rowEncoding basis) _ hn)).comp
    (fp_dedupByFirst e BitEncoding.nat.list _ (FixedFieldArithmetic.fp_equality basis))

end PlanarHom.SourceExponentRepresentatives
