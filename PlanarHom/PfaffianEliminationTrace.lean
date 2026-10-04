import PlanarHom.PfaffianEliminationHeights

/-! An explicit trace theorem for every intermediate matrix of the recovered
executable pivot program. The entry bound below has no invariant hypothesis. -/
namespace PlanarHom.MultiGraph.PfaffianElimination
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- Materialized states visited by the same first-pivot recursion as `run`. -/
def stateTrace (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) :
    List (Matrix (Fin n) (Fin n) F × List (Fin n)) :=
  (A,active) :: match active with
  | [] => []
  | i::xs => match firstPivot A i xs with
    | none => []
    | some (k,j) => stateTrace (storedUpdate A i j) (xs.eraseIdx k)
termination_by active.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)

/-- Every visited state retains the initialized exact original-input minor
certificate and the alternating/nodup state conditions. -/
theorem stateTrace_invariant (original A : Matrix (Fin n) (Fin n) F) (active : List (Fin n))
    (hs : SchurState original A active) (hv : ValidState A active) :
    ∀ B ys, (B,ys) ∈ stateTrace A active → SchurState original B ys ∧ ValidState B ys := by
  induction A, active using run.induct with
  | case1 A =>
    intro B ys hm
    simp only [stateTrace, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩
    exact ⟨hs,hv⟩
  | case2 A i xs h =>
    intro B ys hm
    rw [stateTrace, h] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩
    exact ⟨hs,hv⟩
  | case3 A i xs k j h ih =>
    intro B ys hm
    rw [stateTrace, h] at hm
    rcases List.mem_cons.mp hm with hm | hm
    · rcases Prod.mk.inj hm with ⟨rfl,rfl⟩
      exact ⟨hs,hv⟩
    · apply ih
      · simpa only [storedUpdate_eq] using schurState_pivot original A i xs hs hv h
      · simpa only [storedUpdate_eq] using validState_update A i xs k j hv
      · exact hm

/-- Polynomial intermediate entry size for the actual executable elimination
trace, charged to the exact original nested-list serialization. -/
theorem exists_polynomial_trace_entry_bound [Algebra ℚ F] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ F) :
    ∃ q : Polynomial ℕ, ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)),
      ValidState A active → ∀ B ys, (B,ys) ∈ stateTrace A active → ∀ u v,
      ((Complexity.numberFieldEncoding basis).encode (B u v)).length ≤
        q.eval (PfaffianMinorHeights.matrixInputLength basis A) := by
  obtain ⟨q,hq⟩ := exists_polynomial_schur_entry_bound basis
  refine ⟨q, fun A active hv B ys hm u v => ?_⟩
  exact hq A B ys (stateTrace_invariant A A active (schurState_initial A active) hv B ys hm).1 u v

end PlanarHom.MultiGraph.PfaffianElimination
