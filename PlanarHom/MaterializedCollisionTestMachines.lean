import PlanarHom.MaterializedProductTableMachines
import PlanarHom.FixedLengthProductRecovery

/-! An actual finite collision-consistency test for each input's materialized table. -/
namespace PlanarHom.MaterializedCollisionTestMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [DecidableEq K]

/-- A nonzero source collision with inconsistent retained target values. -/
def badPair (p : (K × K) × (K × K)) : Bool :=
  decide (p.1.1 ≠ 0 ∧ p.1.1 = p.2.1 ∧ p.1.2 ≠ p.2.2)

/-- Every ordered pair is tested, with zero source products ignored. -/
def consistent (table : List (K × K)) : Bool :=
  !(table.any (fun p => table.any (fun q => badPair (p, q))))

theorem consistent_eq_true_iff (table : List (K × K)) : consistent table = true ↔
    ∀ p ∈ table, ∀ q ∈ table, p.1 ≠ 0 → p.1 = q.1 → p.2 = q.2 := by
  constructor
  · intro h p hp q hq hz he
    by_contra ht
    have hbad : badPair (p, q) = true := decide_eq_true ⟨hz, he, ht⟩
    have hq' : table.any (fun q => badPair (p, q)) = true := List.any_eq_true.mpr ⟨q, hq, hbad⟩
    have hp' : table.any (fun p => table.any (fun q => badPair (p, q))) = true :=
      List.any_eq_true.mpr ⟨p, hp, hq'⟩
    simp [consistent, hp'] at h
  · intro h
    cases hh : table.any (fun p => table.any (fun q => badPair (p, q))) with
    | false => simp [consistent, hh]
    | true =>
      obtain ⟨p, hp, hq'⟩ := List.any_eq_true.mp hh
      obtain ⟨q, hq, hbad⟩ := List.any_eq_true.mp hq'
      have hb := of_decide_eq_true hbad
      exact False.elim (hb.2.2 (h p hp q hq hb.1 hb.2.1))

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

theorem fp_badPair : FP (((numberFieldEncoding basis).prod (numberFieldEncoding basis)).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))) BitEncoding.bool (badPair : _ → Bool) := by
  let e := numberFieldEncoding basis
  let input := (e.prod e).prod (e.prod e)
  have hp := fp_fst (e.prod e) (e.prod e)
  have hq := fp_snd (e.prod e) (e.prod e)
  have hps := hp.comp (fp_fst e e)
  have hpt := hp.comp (fp_snd e e)
  have hqs := hq.comp (fp_fst e e)
  have hqt := hq.comp (fp_snd e e)
  have hzero := (hps.pair (fp_const input e (0 : K))).comp (FixedFieldArithmetic.fp_equality basis)
  have hnz := hzero.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hse := (hps.pair hqs).comp (FixedFieldArithmetic.fp_equality basis)
  have hte := (hpt.pair hqt).comp (FixedFieldArithmetic.fp_equality basis)
  have htn := hte.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hlast := (hse.pair htn).comp (fp_bool_gate (fun p => p.1 && p.2))
  exact ((hnz.pair hlast).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
    (fun _ => by simp [badPair])

/-- Nested dynamic context maps and Boolean folds inspect all actual row pairs. -/
theorem fp_consistent : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
    BitEncoding.bool (consistent : List (K × K) → Bool) := by
  let e := (numberFieldEncoding basis).prod (numberFieldEncoding basis)
  have hm := ListPredicateMachines.fp_member e badPair (fp_badPair basis)
  have hs := ((fp_snd e.list e).pair (fp_fst e.list e)).comp hm
  have hmap := ListContextMachines.fp_mapWithContext e.list e BitEncoding.bool
    (fun p : List (K × K) × (K × K) => p.1.any (fun q => badPair (p.2, q))) hs
  have h := (((fp_id e.list).pair (fp_id e.list)).comp hmap).comp
    (ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))
  exact (h.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr
    (fun _ => by simp [consistent, List.any_map])

variable {t : ℕ}

/-- Compute the original product table and decide length-local consistency. -/
def test (p : MaterializedProductTableMachines.Input K t) : Bool :=
  consistent (MaterializedProductTableMachines.products p)

theorem fp_test : FP (MaterializedProductTableMachines.inputEncoding basis t) BitEncoding.bool
    (test : MaterializedProductTableMachines.Input K t → Bool) :=
  (MaterializedProductTableMachines.fp_products basis).comp (fp_consistent basis)

omit [Algebra ℚ K] in
/-- Exact equivalence with the semantic compatibility needed by source (3.7). -/
theorem test_eq_true_iff (p : MaterializedProductTableMachines.Input K t) :
    test p = true ↔ ExponentProductTables.CompatibleAt p.2.1 p.2.2 p.1 := by
  rw [test, consistent_eq_true_iff]
  constructor
  · intro h xs hxs ys hys hz he
    apply h (ExponentProductSemantics.value p.2.1 xs, ExponentProductSemantics.value p.2.2 xs) _
      (ExponentProductSemantics.value p.2.1 ys, ExponentProductSemantics.value p.2.2 ys) _ hz he
    · change _ ∈ ExponentProductTables.products _ _ _
      rw [ExponentProductTables.products_list_form]
      exact List.mem_map.mpr ⟨xs, hxs, rfl⟩
    · change _ ∈ ExponentProductTables.products _ _ _
      rw [ExponentProductTables.products_list_form]
      exact List.mem_map.mpr ⟨ys, hys, rfl⟩
  · intro h row hrow row' hrow' hz he
    exact ExponentProductTables.targets_consistent_at _ _ _ h row row' hrow hrow' hz he

end PlanarHom.MaterializedCollisionTestMachines
