import PlanarHom.OccurrencePfaffianPairings
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

/-!
# Executable pivot elimination on a fixed ambient matrix

This file supplies an executable field-arithmetic program, including deterministic
first-nonzero pivot selection, an array-materialized Schur update, termination,
and its arithmetic schedule.  It does **not** assert that the program computes
the signed pairing expansion.  The recurrence theorem at the end isolates the
algebraic identities needed for that bridge; none is postulated as an axiom.

The cost model counts field additions, subtractions, multiplications and divisions
with unit cost. Constants, comparisons and indexing are not field arithmetic;
zero tests are counted separately. These bounds are not bit-complexity or FP
claims. Each pivot explicitly materializes all ambient `n * n` matrix entries.
-/

namespace PlanarHom.MultiGraph
namespace PfaffianElimination

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- The first nonzero entry, with its zero-based position in the active tail. -/
def firstPivot (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    List (Fin n) → Option (ℕ × Fin n)
  | [] => none
  | j :: js => if A i j = 0 then
      (firstPivot A i js).map (fun p => (p.1 + 1, p.2))
    else some (0, j)

@[simp] theorem firstPivot_nil (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    firstPivot A i [] = none := rfl

theorem firstPivot_none_iff (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) : firstPivot A i xs = none ↔ ∀ j ∈ xs, A i j = 0 := by
  induction xs with
  | nil => simp [firstPivot]
  | cons j js ih =>
    by_cases h : A i j = 0
    · simp [firstPivot, h, ih]
    · simp [firstPivot, h]

/-- A selected pivot is nonzero, is at the claimed list position, and every
preceding entry in that row vanishes. -/
theorem firstPivot_some_spec (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) :
    A i j ≠ 0 ∧ xs[k]? = some j ∧ ∀ t < k, ∀ v, xs[t]? = some v → A i v = 0 := by
  induction xs generalizing k with
  | nil => simp [firstPivot] at h
  | cons v vs ih =>
    by_cases hv : A i v = 0
    · simp only [firstPivot, hv, if_true, Option.map_eq_some_iff] at h
      obtain ⟨⟨l, w⟩, hp, heq⟩ := h
      cases heq
      obtain ⟨hnz, hget, hpre⟩ := ih hp
      refine ⟨hnz, by simpa using hget, ?_⟩
      intro t ht u hu
      cases t with
      | zero => simpa using (Option.some.inj hu ▸ hv)
      | succ t => exact hpre t (by omega) u (by simpa using hu)
    · simp only [firstPivot, hv, if_false, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hv, rfl, by omega⟩

theorem firstPivot_nonzero (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) : A i j ≠ 0 :=
  (firstPivot_some_spec A i xs h).1

theorem firstPivot_index_lt (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) : k < xs.length := by
  have hget := (firstPivot_some_spec A i xs h).2.1
  exact List.getElem?_eq_some_iff.mp hget |>.1

/-- The rational Schur update, without any partial division operation. The
selected pivot theorem supplies nonvanishing whenever this update is used. -/
def pivotUpdate (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix (Fin n) (Fin n) F := fun u v =>
  A u v - (A i u * A j v) / A i j + (A j u * A i v) / A i j

/-- Explicit array-backed storage prevents an iterated matrix closure from
recomputing earlier updates when an entry is read. -/
def materialize (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  let entries : Vector (Vector F n) n := Vector.ofFn (fun i => Vector.ofFn (A i))
  fun i j => entries[i.val][j.val]

omit [Field F] [DecidableEq F] in
@[simp] theorem materialize_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    materialize A i j = A i j := by simp [materialize]

omit [Field F] [DecidableEq F] in
@[simp] theorem materialize_eq (A : Matrix (Fin n) (Fin n) F) : materialize A = A := by
  ext i j
  exact materialize_apply A i j

/-- Both coordinates range over the full ambient `Fin n`. -/
def storedUpdate (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix (Fin n) (Fin n) F := materialize (pivotUpdate A i j)

omit [DecidableEq F] in
@[simp] theorem storedUpdate_eq (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    storedUpdate A i j = pivotUpdate A i j := materialize_eq _

omit [DecidableEq F] in
theorem pivotUpdate_skew (A : Matrix (Fin n) (Fin n) F) (i j : Fin n)
    (hA : ∀ u v, A v u = -A u v) :
    ∀ u v, pivotUpdate A i j v u = -pivotUpdate A i j u v := by
  intro u v
  simp only [pivotUpdate, hA v u, div_eq_mul_inv]
  ring

omit [DecidableEq F] in
theorem pivotUpdate_diag (A : Matrix (Fin n) (Fin n) F) (i j : Fin n)
    (hA : ∀ u, A u u = 0) : ∀ u, pivotUpdate A i j u u = 0 := by
  intro u
  simp only [pivotUpdate, hA u, div_eq_mul_inv]
  ring

/-- A sign is selected by natural-number parity, rather than computing a power
by a sequence of field multiplications. -/
def pivotSign (k : ℕ) : F := if Even k then 1 else -1

omit [DecidableEq F] in
theorem pivotSign_eq (k : ℕ) : pivotSign (F := F) k = (-1 : F) ^ k :=
  (neg_one_pow_eq_ite).symm

/-- Schedule of the materialized program. `arithmeticOps` excludes zero tests,
which have their own counter. -/
structure RunResult (F : Type*) where
  value : F
  arithmeticOps : ℕ
  zeroTests : ℕ
  pivots : ℕ
  deriving DecidableEq, Repr

/-- Two products, two divisions, one subtraction and one addition per entry,
then two scalar multiplications for the signed recursive value. -/
def stepArithmetic (n : ℕ) : ℕ := 6 * n * n + 2

/-- Executable first-pivot elimination. The recursive active list removes its
head and the selected partner. The ambient dimension does not change. -/
def run (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) : RunResult F :=
  match active with
  | [] => ⟨1, 0, 0, 0⟩
  | i :: xs =>
    match firstPivot A i xs with
    | none => ⟨0, 0, xs.length, 0⟩
    | some (k, j) =>
      let next := run (storedUpdate A i j) (xs.eraseIdx k)
      ⟨pivotSign k * A i j * next.value,
        stepArithmetic n + next.arithmeticOps,
        k + 1 + next.zeroTests, 1 + next.pivots⟩
termination_by active.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)

/-- Public scalar evaluator. It is executable for any field with computable
operations and decidable equality; no classical choice is used by the program. -/
def evaluate (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) : F :=
  (run (materialize A) active).value

@[simp] theorem run_nil (A : Matrix (Fin n) (Fin n) F) :
    run A [] = ⟨1, 0, 0, 0⟩ := by rw [run]

theorem run_cons_noPivot (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) (h : ∀ j ∈ xs, A i j = 0) :
    run A (i :: xs) = ⟨0, 0, xs.length, 0⟩ := by
  rw [run, (firstPivot_none_iff A i xs).2 h]

theorem run_cons_pivot (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) :
    run A (i :: xs) =
      let next := run (pivotUpdate A i j) (xs.eraseIdx k)
      ⟨(-1 : F)^k * A i j * next.value,
        stepArithmetic n + next.arithmeticOps,
        k + 1 + next.zeroTests, 1 + next.pivots⟩ := by
  rw [run, h]
  simp only [storedUpdate_eq, pivotSign_eq]

@[simp] theorem evaluate_nil (A : Matrix (Fin n) (Fin n) F) :
    evaluate A [] = 1 := by simp [evaluate]

theorem evaluate_cons_noPivot (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) (h : ∀ j ∈ xs, A i j = 0) :
    evaluate A (i :: xs) = 0 := by
  simp only [evaluate, materialize_eq, run_cons_noPivot A i xs h]

@[simp] theorem evaluate_singleton (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    evaluate A [i] = 0 := evaluate_cons_noPivot A i [] (by simp)

theorem evaluate_cons_pivot (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) :
    evaluate A (i :: xs) = (-1 : F)^k * A i j *
      evaluate (pivotUpdate A i j) (xs.eraseIdx k) := by
  simp only [evaluate, materialize_eq, run_cons_pivot A i xs h]

theorem evaluate_zero (active : List (Fin n)) :
    evaluate (0 : Matrix (Fin n) (Fin n) F) active = if active = [] then 1 else 0 := by
  cases active with
  | nil => simp
  | cons i xs =>
    simpa using evaluate_cons_noPivot (0 : Matrix (Fin n) (Fin n) F) i xs (by intros; rfl)


/-- A two-vertex active list has the expected entry, including the zero case. -/
@[simp] theorem evaluate_pair (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    evaluate A [i, j] = A i j := by
  by_cases h : A i j = 0
  · rw [evaluate_cons_noPivot A i [j] (by simpa using h), h]
  · have hp : firstPivot A i [j] = some (0, j) := by simp [firstPivot, h]
    rw [evaluate_cons_pivot A i [j] hp]
    simp

/-- Executable regression: the first row skips a zero entry, so the pivot is at
odd tail position; the update also uses negative and fractional coefficients. -/
theorem signed_four_vertex_regression :
    evaluate
      (![![(0 : ℚ), 0, 2, -3], ![0, 0, 5, 7],
         ![-2, -5, 0, 11], ![3, -7, -11, 0]] : Matrix (Fin 4) (Fin 4) ℚ)
      [0, 1, 2, 3] = -29 := by
  let A : Matrix (Fin 4) (Fin 4) ℚ :=
    ![![0, 0, 2, -3], ![0, 0, 5, 7], ![-2, -5, 0, 11], ![3, -7, -11, 0]]
  change evaluate A [0, 1, 2, 3] = -29
  have hp : firstPivot A 0 [1, 2, 3] = some (1, 2) := by decide
  rw [evaluate_cons_pivot A 0 [1, 2, 3] hp]
  change (-1 : ℚ)^1 * 2 * evaluate (pivotUpdate A 0 2) [1, 3] = -29
  rw [evaluate_pair]
  change (-1 : ℚ)^1 * 2 * (7 - (0 * 11) / 2 + (-5 * -3) / 2) = -29
  norm_num

/-- Exact arithmetic accounting, a two-vertices-per-pivot bound, and a quadratic
bound on zero tests in the explicit schedule. -/
theorem run_schedule_bounds (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) :
    (run A active).arithmeticOps = stepArithmetic n * (run A active).pivots ∧
    2 * (run A active).pivots ≤ active.length ∧
    (run A active).zeroTests ≤ active.length * active.length := by
  induction A, active using run.induct with
  | case1 A => simp
  | case2 A i xs h =>
    rw [run, h]
    simp only [List.length_cons]
    constructor
    · simp
    constructor
    · omega
    · nlinarith
  | case3 A i xs k j h ih =>
    have hk := firstPivot_index_lt A i xs h
    have hlen := List.length_eraseIdx_of_lt hk
    simp only [storedUpdate_eq] at ih
    rw [run_cons_pivot A i xs h]
    dsimp only
    rcases ih with ⟨harith, hpiv, htests⟩
    constructor
    · rw [harith]
      ring
    constructor
    · simp only [List.length_cons]
      rw [hlen] at hpiv
      omega
    · have hle := List.length_eraseIdx_le xs k
      simp only [List.length_cons]
      nlinarith

/-- Cubic ambient-dimension bound for a duplicate-free active list. This is
only the stated unit-cost field-arithmetic schedule, not a machine-time bound. -/
theorem run_arithmetic_le_cubic (A : Matrix (Fin n) (Fin n) F)
    (active : List (Fin n)) (hactive : active.Nodup) :
    (run A active).arithmeticOps ≤ (6 * n * n + 2) * n := by
  obtain ⟨ha, hp, _⟩ := run_schedule_bounds A active
  have hlen : active.length ≤ n := by simpa using hactive.length_le_card
  rw [ha]
  exact Nat.mul_le_mul_left _ (by omega)

theorem run_zeroTests_le_square (A : Matrix (Fin n) (Fin n) F)
    (active : List (Fin n)) (hactive : active.Nodup) :
    (run A active).zeroTests ≤ n * n := by
  have htests := (run_schedule_bounds A active).2.2
  have hlen : active.length ≤ n := by simpa using hactive.length_le_card
  exact htests.trans (Nat.mul_le_mul hlen hlen)

/-- The hypotheses supplied to an algebraic correctness proof.  Diagonal
vanishing is separate from skewness, so characteristic two is not excluded. -/
def ValidState (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) : Prop :=
  (∀ u v, A v u = -A u v) ∧ (∀ u, A u u = 0) ∧ active.Nodup

omit [DecidableEq F] in
theorem validState_update (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) (k : ℕ) (j : Fin n) (h : ValidState A (i :: xs)) :
    ValidState (pivotUpdate A i j) (xs.eraseIdx k) := by
  exact ⟨pivotUpdate_skew A i j h.1, pivotUpdate_diag A i j h.2.1,
    h.2.2.tail.eraseIdx k⟩

/-- A proved induction principle for the executable evaluator. The semantic
pivot recurrence is an explicit hypothesis and is not discharged in this file.  A caller must
prove the displayed base, vanishing-row, and Schur-pivot equations for its own
semantic quantity. No algebraic identity is assumed by the program itself. -/
theorem evaluate_eq_of_pivot_recurrence
    (Φ : Matrix (Fin n) (Fin n) F → List (Fin n) → F)
    (Inv : Matrix (Fin n) (Fin n) F → List (Fin n) → Prop)
    (hnil : ∀ A, Inv A [] → Φ A [] = 1)
    (hzero : ∀ A i xs, Inv A (i :: xs) → (∀ j ∈ xs, A i j = 0) →
      Φ A (i :: xs) = 0)
    (hstep : ∀ A i xs k j, Inv A (i :: xs) → firstPivot A i xs = some (k, j) →
      Φ A (i :: xs) = (-1 : F)^k * A i j * Φ (pivotUpdate A i j) (xs.eraseIdx k))
    (hpreserve : ∀ A i xs k j, Inv A (i :: xs) → firstPivot A i xs = some (k, j) →
      Inv (pivotUpdate A i j) (xs.eraseIdx k))
    (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) (hInv : Inv A active) :
    evaluate A active = Φ A active := by
  induction A, active using run.induct with
  | case1 A => simpa using (hnil A hInv).symm
  | case2 A i xs h =>
    have hz := (firstPivot_none_iff A i xs).1 h
    rw [evaluate_cons_noPivot A i xs hz, hzero A i xs hInv hz]
  | case3 A i xs k j h ih =>
    simp only [storedUpdate_eq] at ih
    rw [evaluate_cons_pivot A i xs h,
      ih (hpreserve A i xs k j hInv h), hstep A i xs k j hInv h]


section OrderedListBridge
variable {V : Type*} [LinearOrder V]

/-- In a strictly ordered list, the position of a vertex is exactly the number
of listed vertices below it. This uses list positions, not ambient labels. -/
theorem sorted_filter_lt_card (xs : List V) (hs : xs.Pairwise (· < ·))
    {k : ℕ} {j : V} (hget : xs[k]? = some j) :
    (xs.toFinset.filter (fun v => v < j)).card = k := by
  induction xs generalizing k with
  | nil => simp at hget
  | cons v vs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases k with
    | zero =>
      have hvj : v = j := Option.some.inj hget
      subst j
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp hu
      rcases List.mem_cons.mp (List.mem_toFinset.mp hm) with rfl | hm
      · exact lt_irrefl _ hlt
      · exact (not_lt_of_ge (hhead u hm).le) hlt
    | succ k =>
      have hget' : vs[k]? = some j := hget
      have hvj : v < j := hhead j (List.mem_of_getElem? hget')
      have hn : v ∉ vs.toFinset := by
        intro hmem
        exact lt_irrefl _ (hhead v (List.mem_toFinset.mp hmem))
      rw [List.toFinset_cons, Finset.filter_insert, if_pos hvj,
        Finset.card_insert_of_notMem (fun hm => hn (Finset.mem_filter.mp hm).1),
        ih htail hget']

/-- Erasing a known position of a duplicate-free list removes exactly its
vertex from the associated finite set. -/
theorem nodup_eraseIdx_toFinset (xs : List V) (hxs : xs.Nodup)
    {k : ℕ} {j : V} (hget : xs[k]? = some j) :
    (xs.eraseIdx k).toFinset = xs.toFinset.erase j := by
  obtain ⟨hk, hj⟩ := List.getElem?_eq_some_iff.mp hget
  rw [← hxs.erase_getElem k hk, hj]
  ext v
  simp [hxs.mem_erase_iff]

/-- Removing a pivot partner preserves the active vertex order. -/
theorem sorted_eraseIdx {i : V} {xs : List V}
    (hs : (i :: xs).Pairwise (· < ·)) (k : ℕ) :
    (xs.eraseIdx k).Pairwise (· < ·) := hs.tail.eraseIdx k

end OrderedListBridge

/-- The program's sign exponent is exactly the active-set between-cardinality
used in the actual signed pairing expansion. -/
theorem firstPivot_between_card (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) (hs : (i :: xs).Pairwise (· < ·)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) :
    ((i :: xs).toFinset.filter (fun v => i < v ∧ v < j)).card = k := by
  have hfilter : xs.toFinset.filter (fun v => i < v ∧ v < j) =
      xs.toFinset.filter (fun v => v < j) := by
    apply Finset.filter_congr
    intro v hv
    simp [(List.pairwise_cons.mp hs).1 v (List.mem_toFinset.mp hv)]
  simp only [List.toFinset_cons, Finset.filter_insert, lt_self_iff_false, false_and, if_false]
  rw [hfilter]
  exact sorted_filter_lt_card xs hs.tail (firstPivot_some_spec A i xs h).2.1

/-- The executable residual list and the semantic residual support erase the
same two vertices, without changing their inherited order. -/
theorem firstPivot_remaining_toFinset (A : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (xs : List (Fin n)) (hs : (i :: xs).Pairwise (· < ·)) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k, j)) :
    (xs.eraseIdx k).toFinset = (((i :: xs).toFinset).erase i).erase j := by
  have hnodup : (i :: xs).Nodup := hs.imp (fun hlt => hlt.ne)
  rw [nodup_eraseIdx_toFinset xs hnodup.tail (firstPivot_some_spec A i xs h).2.1]
  simp [List.toFinset_cons, List.mem_toFinset, hnodup.notMem]

end PfaffianElimination
end PlanarHom.MultiGraph
