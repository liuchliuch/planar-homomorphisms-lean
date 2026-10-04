import PlanarHom.BooleanNormSampleSearch
import PlanarHom.BooleanFieldCollisionMachines
import PlanarHom.DependentMonomialMachines

/-! The grid selector specialized to the actual fixed-field collision machine. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanNormSampleMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BooleanNormSampleSearch
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension b : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

def counts (p : Input) (i : Fin b) : ℕ := min p.2.1 (p.2.2.getD i.val 0)
def leftCounts (p : Input) (kl : CountPair) (i : Fin b) : ℕ :=
  min (counts p i) (kl.1.getD i.val 0)
def rightCounts (p : Input) (kl : CountPair) (i : Fin b) : ℕ :=
  min (counts p i) (kl.2.getD i.val 0)

def raw (r : Row) : BooleanFieldCollisionMachines.Input b :=
  (r.1.1.2.1,(r.1.2,((fun i => r.1.1.2.2.getD i.val 0),
    ((fun i => r.2.1.getD i.val 0),(fun i => r.2.2.getD i.val 0)))))

def eligible (a : Fin b → K) (p : Input) (kl : CountPair) : Prop :=
  ∃ i, a i ≠ 0 ∧ leftCounts p kl i ≠ rightCounts p kl i

def normValue (c a w : Fin b → K) (r : Row) : K :=
  BooleanFieldCollisionMachines.evaluate c a w (raw r)

omit [DecidableEq K] in
theorem normValue_eq (c a w : Fin b → K) (r : Row) :
    normValue c a w r = BooleanFieldCollision.collision c a w (algebraMap ℚ K r.1.2)
      (counts r.1.1) (leftCounts r.1.1 r.2) (rightCounts r.1.1 r.2) := rfl

def bad (c a w : Fin b → K) (r : Row) : Bool :=
  decide (eligible a r.1.1 r.2 ∧ normValue c a w r = 0)

private theorem fp_context : FP rowEncoding inputEncoding (fun r : Row => r.1.1) :=
  (fp_fst (inputEncoding.prod BitEncoding.rat) pairEncoding).comp
    (fp_fst inputEncoding BitEncoding.rat)

private theorem fp_cap : FP rowEncoding BitEncoding.unaryNat (fun r : Row => r.1.1.2.1) :=
  (fp_context.comp (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list))).comp
    (fp_fst BitEncoding.unaryNat BitEncoding.nat.list)

private theorem fp_countList : FP rowEncoding BitEncoding.nat.list (fun r : Row => r.1.1.2.2) :=
  (fp_context.comp (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list))).comp
    (fp_snd BitEncoding.unaryNat BitEncoding.nat.list)

private theorem fp_leftList : FP rowEncoding BitEncoding.nat.list (fun r : Row => r.2.1) :=
  (fp_snd (inputEncoding.prod BitEncoding.rat) pairEncoding).comp
    (fp_fst BitEncoding.nat.list BitEncoding.nat.list)

private theorem fp_rightList : FP rowEncoding BitEncoding.nat.list (fun r : Row => r.2.2) :=
  (fp_snd (inputEncoding.prod BitEncoding.rat) pairEncoding).comp
    (fp_snd BitEncoding.nat.list BitEncoding.nat.list)

theorem fp_raw : FP rowEncoding (BooleanFieldCollisionMachines.inputEncoding b) (raw (b := b)) := by
  have hq := (fp_fst (inputEncoding.prod BitEncoding.rat) pairEncoding).comp
    (fp_snd inputEncoding BitEncoding.rat)
  have hn := FixedVectorMachines.fp_assemble rowEncoding BitEncoding.nat b
    (fun r i => r.1.1.2.2.getD i.val 0) (fun i => fp_countList.comp
      (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))
  have hk := FixedVectorMachines.fp_assemble rowEncoding BitEncoding.nat b
    (fun r i => r.2.1.getD i.val 0) (fun i => fp_leftList.comp
      (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))
  have hl := FixedVectorMachines.fp_assemble rowEncoding BitEncoding.nat b
    (fun r i => r.2.2.getD i.val 0) (fun i => fp_rightList.comp
      (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))
  exact fp_cap.pair (hq.pair (hn.pair (hk.pair hl)))

theorem fp_counts (i : Fin b) :
    FP rowEncoding BitEncoding.unaryNat (fun r : Row => counts r.1.1 i) :=
  (fp_cap.pair (fp_countList.comp (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))).comp
    ⟨BoundedUnaryMachines.computer⟩

theorem fp_leftCounts (i : Fin b) :
    FP rowEncoding BitEncoding.unaryNat (fun r : Row => leftCounts r.1.1 r.2 i) :=
  ((fp_counts i).pair (fp_leftList.comp (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))).comp
    ⟨BoundedUnaryMachines.computer⟩

theorem fp_rightCounts (i : Fin b) :
    FP rowEncoding BitEncoding.unaryNat (fun r : Row => rightCounts r.1.1 r.2 i) :=
  ((fp_counts i).pair (fp_rightList.comp (DependentMonomialMachines.fp_getD BitEncoding.nat 0 i.val))).comp
    ⟨BoundedUnaryMachines.computer⟩

omit [Algebra ℚ K] in
theorem fp_eligible (a : Fin b → K) :
    FP rowEncoding BitEncoding.bool (fun r : Row => decide (eligible a r.1.1 r.2)) := by
  have hi (i : Fin b) :=
    (((fp_leftCounts i).comp UnaryNatConversionMachine.fp_conversion).pair
      ((fp_rightCounts i).comp UnaryNatConversionMachine.fp_conversion)).comp NatListSumMachines.fp_equal
  have hor (i : Fin b) := ((fp_const rowEncoding BitEncoding.bool (decide (a i=0))).pair (hi i)).comp
    (fp_bool_gate (fun p => p.1 || p.2))
  have hall := FiniteRationalCircuits.fp_all rowEncoding Finset.univ
    (fun r i => decide (a i=0 ∨ leftCounts r.1.1 r.2 i=rightCounts r.1.1 r.2 i))
    (fun i => (hor i).congr (fun r => by simp))
  apply (hall.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr
  intro r
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Finset.mem_univ, forall_const, not_forall, not_or, eligible]

omit [DecidableEq K] in
theorem fp_normValue (c a w : Fin b → K) :
    FP rowEncoding (numberFieldEncoding basis) (normValue c a w) :=
  fp_raw.comp (BooleanFieldCollisionMachines.fp_evaluate basis c a w)

include basis in
/-- Every predicate bit comes from the actual norm machine and exact arithmetic. -/
theorem fp_bad (c a w : Fin b → K) : FP rowEncoding BitEncoding.bool (bad c a w) := by
  have hz := ((fp_normValue basis c a w).pair (fp_const rowEncoding (numberFieldEncoding basis) 0)).comp
    (FixedFieldArithmetic.fp_equality basis)
  exact (((fp_eligible a).pair hz).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
    (fun r => by simp [bad])

def candidates (c a w : Fin b → K) : Input → List ℚ :=
  BooleanNormSampleSearch.candidates b (bad c a w)
def search (c a w : Fin b → K) : Input → ℚ := BooleanNormSampleSearch.search b (bad c a w)

include basis in
/-- Actual polynomial bit cost, with no collision-tester oracle hypothesis. -/
theorem fp_candidates (c a w : Fin b → K) :
    FP inputEncoding BitEncoding.rat.list (candidates c a w) :=
  BooleanNormSampleSearch.fp_candidates b (bad c a w) (fp_bad basis c a w)

include basis in
theorem fp_search (c a w : Fin b → K) : FP inputEncoding BitEncoding.rat (search c a w) :=
  BooleanNormSampleSearch.fp_search b (bad c a w) (fp_bad basis c a w)

theorem mem_candidates_iff (c a w : Fin b → K) (p : Input) (q : ℚ) :
    q ∈ candidates c a w p ↔ q ∈ BooleanExceptionalGrid.rationalGrid p.1 ∧
      ∀ kl ∈ pairs b p, eligible a p kl → normValue c a w ((p,q),kl) ≠ 0 := by
  simp [candidates, BooleanNormSampleSearch.mem_candidates_iff, bad]

end PlanarHom.BooleanNormSampleMachines
