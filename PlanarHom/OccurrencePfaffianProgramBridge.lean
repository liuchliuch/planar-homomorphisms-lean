import PlanarHom.OccurrencePfaffianEliminationAlgorithm
import PlanarHom.OccurrencePfaffianEvaluationProgram

/-! NEW reconstruction. The row-list program implements the recovered
first-nonzero pivot program exactly; this layer does not replace the separate
signed-pairing Schur identity. -/
namespace PlanarHom.PfaffianList
open MultiGraph.PfaffianElimination
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {n : ℕ}

 theorem zipIdx_ofFn {A : Type} {n : ℕ} (f : Fin n → A) :
    (List.ofFn f).zipIdx = List.ofFn (fun i => (f i,i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

 theorem updateGrid_matrixRows (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    updateGrid (matrixRows A) i.val j.val = matrixRows (pivotUpdate A i j) := by
  simp only [updateGrid, matrixRows, zipIdx_ofFn, List.map_ofFn, Function.comp_def,
    updateRow, zipIdx_ofFn, List.map_ofFn]
  congr 1
  funext u
  congr 1
  funext v
  simp [updateEntry, entry, lookup, pivotUpdate]

 theorem candidates_cons (g : Grid K) (i v : ℕ) (xs : List ℕ) :
    candidates g i (v :: xs) =
      if entry g i v = 0 then
        (candidates g i xs).map (fun q => (q.1,q.2+1))
      else (v,0) :: (candidates g i xs).map (fun q => (q.1,q.2+1)) := by
  by_cases h : entry g i v = 0 <;>
    simp [candidates, List.zipIdx_cons, List.zipIdx_succ, List.filter_map, h,
      List.map_filter, Function.comp_def]

 theorem candidates_head_matrixRows (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (xs : List (Fin n)) :
    (candidates (matrixRows A) i.val (xs.map Fin.val)).head? =
      (firstPivot A i xs).map (fun p => (p.2.val,p.1)) := by
  induction xs with
  | nil => simp [candidates, firstPivot]
  | cons v xs ih =>
    simp only [List.map_cons, candidates_cons, entry_matrixRows]
    by_cases h : A i v = 0
    · simp [h, firstPivot, ih, Option.map_map, Function.comp_def]
    · simp [h, firstPivot]

 theorem step_matrixRows_nil (A : Matrix (Fin n) (Fin n) K) (a : K) :
    step (matrixRows A, (([] : List (Fin n)).map Fin.val,a)) =
      (matrixRows A,([],a)) := by simp

 theorem step_matrixRows_noPivot (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (xs : List (Fin n)) (a : K) (h : firstPivot A i xs = none) :
    step (matrixRows A,((i::xs).map Fin.val,a)) = (matrixRows A,([],0)) := by
  have hc : candidates (matrixRows A) i.val (xs.map Fin.val) = [] := by
    have hh := candidates_head_matrixRows A i xs
    rw [h] at hh
    simpa using hh
  simp [step, pivotCandidates, headVertex, tailVertices, hc]

 theorem step_matrixRows_pivot (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (xs : List (Fin n)) (a : K) {k : ℕ} {j : Fin n}
    (h : firstPivot A i xs = some (k,j)) :
    step (matrixRows A,((i::xs).map Fin.val,a)) =
      (matrixRows (pivotUpdate A i j),
        ((xs.eraseIdx k).map Fin.val,a*((-1:K)^k*A i j))) := by
  have hh := candidates_head_matrixRows A i xs
  rw [h] at hh
  change (candidates (matrixRows A) i.val (xs.map Fin.val)).head? = some (j.val,k) at hh
  have hc : candidates (matrixRows A) i.val (xs.map Fin.val) ≠ [] := by
    intro hc
    simp [hc] at hh
  have hd : (candidates (matrixRows A) i.val (xs.map Fin.val)).headD (0,0) = (j.val,k) := by
    simp only [List.headD_eq_head?_getD, hh, Option.getD_some]
  simp only [step, List.map_cons, List.cons_ne_nil, ↓reduceIte,
    pivotCandidates, headVertex, List.headD_cons, tailVertices, List.tail_cons, hc]
  simp only [pivotStep, pivotChoice, pivotCandidates, headVertex, tailVertices,
    List.headD_cons, List.tail_cons, hd, updateGrid_matrixRows, eraseIndex_eq,
    List.eraseIdx_map, sign_eq, entry_matrixRows]

 theorem iterate_eq_run (A : Matrix (Fin n) (Fin n) K) (active : List (Fin n))
    (a : K) (t : ℕ) (ht : active.length ≤ t) :
    (step^[t] (matrixRows A,(active.map Fin.val,a))).2.2 = a * (run A active).value := by
  induction t generalizing A active a with
  | zero =>
    have he : active = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero ht)
    subst active
    simp
  | succ t ih =>
    cases active with
    | nil =>
      rw [iterate_completed _ (by rfl)]
      simp
    | cons i xs =>
      rw [Function.iterate_succ_apply]
      cases hp : firstPivot A i xs with
      | none =>
        rw [step_matrixRows_noPivot A i xs a hp, iterate_completed _ (by rfl)]
        rw [run, hp]
        simp
      | some q =>
        rcases q with ⟨k,j⟩
        rw [step_matrixRows_pivot A i xs a hp]
        rw [ih (pivotUpdate A i j) (xs.eraseIdx k) _
          (by have he := List.length_eraseIdx_le xs k; simp only [List.length_cons] at ht; omega)]
        rw [run_cons_pivot A i xs hp]
        dsimp only
        ring

 theorem evaluateRawGrid_eq_elimination (A : Matrix (Fin n) (Fin n) K) :
    evaluateRawGrid (matrixRows A) = evaluate A (List.finRange n) := by
  have hh := iterate_eq_run A (List.finRange n) 1 n (by simp)
  simpa [evaluateRawGrid, initialState, evaluate, materialize_eq, matrixRows_length] using hh


 theorem evaluateGrid_eq_elimination (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    evaluateGrid (matrixRows A) = evaluate A (List.finRange n) := by
  rw [evaluateGrid, normalizeGrid_matrixRows A hskew hdiag, evaluateRawGrid_eq_elimination]

end PlanarHom.PfaffianList
