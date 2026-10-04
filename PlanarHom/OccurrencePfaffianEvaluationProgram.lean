import PlanarHom.OccurrencePfaffianGridNormalization
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.OfFn

/-! NEW reconstruction. The literal runtime-dimension pivot program and its
termination guarantee on all raw grids, including empty and ragged input. -/

namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def initialState (g : Grid K) : State K := (g,(List.range g.length,1))

def evaluateRawGrid (g : Grid K) : K := (step^[g.length] (initialState g)).2.2

/-- The public total evaluator first materializes an alternating square grid. -/
def evaluateGrid (g : Grid K) : K := evaluateRawGrid (normalizeGrid g)

/-- Literal row-major materialization of a finite matrix. -/
def matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Grid K :=
  List.ofFn (fun i => List.ofFn (A i))

 theorem fp_initialState : FP (gridEncoding basis) (stateEncoding basis) (initialState (K := K)) := by
  have hn := ListUnaryLengthMachine.fp_length (numberFieldEncoding basis).list
  have hr := hn.comp UnaryArithmeticMachines.fp_range
  exact (fp_id (gridEncoding basis)).pair
    (hr.pair (fp_const (gridEncoding basis) (numberFieldEncoding basis) 1))

@[simp] theorem matrixRows_length {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (matrixRows A).length = n := by simp [matrixRows]

@[simp] theorem entry_matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    entry (matrixRows A) i.val j.val = A i j := by
  simp [entry, lookup, matrixRows]

@[simp] theorem step_completed (g : Grid K) (a : K) : step (g,([],a)) = (g,([],a)) := by
  simp [step]

 theorem step_active_length (s : State K) : (step s).2.1.length ≤ s.2.1.length := by
  unfold step
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.zero_le _
    · simp only [pivotStep, eraseIndex_eq, tailVertices]
      exact (List.length_eraseIdx_le _ _).trans (by simp)

 theorem step_active_length_lt (s : State K) (hs : s.2.1 ≠ []) :
    (step s).2.1.length < s.2.1.length := by
  unfold step
  rw [if_neg hs]
  split
  · exact List.length_pos_iff.mpr hs
  · simp only [pivotStep, eraseIndex_eq, tailVertices]
    exact (List.length_eraseIdx_le _ _).trans_lt (by have h := List.length_pos_iff.mpr hs; simp only [List.length_tail]; omega)

 theorem iterate_completed (s : State K) (hs : s.2.1 = []) (t : ℕ) :
    step^[t] s = s := by
  apply Function.iterate_fixed
  rcases s with ⟨g,xs,a⟩
  change xs = [] at hs
  subst xs
  exact step_completed g a

/-- Every nonterminal pass removes at least the active head; therefore the
actual bounded iterator reaches a terminal state by the initial active length. -/
 theorem iterate_terminates (s : State K) (t : ℕ) (ht : s.2.1.length ≤ t) :
    (step^[t] s).2.1 = [] := by
  induction t generalizing s with
  | zero => simpa using List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero ht)
  | succ t ih =>
    by_cases hs : s.2.1 = []
    · rw [iterate_completed s hs]
      exact hs
    · rw [Function.iterate_succ_apply]
      exact ih (step s) (by have h := step_active_length_lt s hs; omega)

 theorem evaluateRawGrid_terminated (g : Grid K) :
    (step^[g.length] (initialState g)).2.1 = [] :=
  iterate_terminates _ _ (by simp [initialState])

 theorem evaluateRawGrid_stable (g : Grid K) (extra : ℕ) :
    (step^[g.length + extra] (initialState g)).2.2 = evaluateRawGrid g := by
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_completed _ (evaluateRawGrid_terminated g) extra]
  rfl 


 theorem normalizeGrid_eq_matrixRows (g : Grid K) :
    normalizeGrid g = matrixRows (fun (i j : Fin g.length) => skewEntry g i.val j.val) := by
  simp only [normalizeGrid, matrixRows, List.ofFn_eq_map]
  rw [← List.map_coe_finRange g.length]
  simp only [List.map_map, Function.comp_def]

 theorem normalizeGrid_matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    normalizeGrid (matrixRows A) = matrixRows A := by
  simp only [normalizeGrid, matrixRows_length]
  simp only [matrixRows, List.ofFn_eq_map]
  rw [← List.map_coe_finRange n]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  apply List.map_congr_left
  intro j hj
  suffices hh : skewEntry (matrixRows A) i.val j.val = A i j by
    simpa only [matrixRows, List.ofFn_eq_map] using hh
  unfold skewEntry
  simp only [entry_matrixRows]
  split_ifs with hij hji
  · rfl
  · rw [hskew, neg_neg]
  · have he : i = j := Fin.ext (by omega)
    subst j
    exact (hdiag i).symm

end PlanarHom.PfaffianList
