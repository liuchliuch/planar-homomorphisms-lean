import PlanarHom.PfaffianPivotShear
import PlanarHom.OccurrencePfaffianShear

/-! Correctness of the executable Pfaffian elimination against the literal
signed pairing expansion, using proved simultaneous row/column shears. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {V F : Type*} [LinearOrder V] [Fintype V] [Field F]

/-- Finite elementary congruences preserve the literal supported pairing sum. -/
theorem supportedPfaffian_partialSourceShear (S : Finset V) (A : Matrix V V F)
    (source : V) (T : Finset V) (c : V → F) (hs : source∈S) (hT : T ⊆ S.erase source)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u=0) :
    supportedPfaffian S (partialSourceShear A source T c) = supportedPfaffian S A := by
  induction T using Finset.induction_on with
  | empty => rw [partialSourceShear_empty]
  | @insert target T ht ih =>
    have htarget := Finset.mem_erase.mp (hT (Finset.mem_insert_self _ _))
    have hsub : T ⊆ S.erase source := fun x hx => hT (Finset.mem_insert_of_mem hx)
    have hsource : source ∉ T := fun hh => Finset.notMem_erase source S (hsub hh)
    rw [partialSourceShear_insert A source target T c ht hsource (hdiag source)]
    have hstep := supportedPfaffian_elementaryShear S
      (partialSourceShear A source T c) source target (c target) hs htarget.2 htarget.1.symm
      (sourceShear_skew A source _ hskew) (sourceShear_diag A source _ hskew hdiag)
    change supportedPfaffian S (elementaryShear (partialSourceShear A source T c) source target (c target)) = _ at hstep
    rw [hstep]
    exact ih hsub

/-- Genuine Schur-pivot identity for the literal signed pairing Pfaffian. -/
theorem supportedPfaffian_pivot (S : Finset V) (A : Matrix V V F) (i j : V)
    (hi : i∈S) (hj : j∈S) (hij : i<j) (hmin : ∀ v∈S, i≤v)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u=0) (hp : A i j≠0) :
    supportedPfaffian S A =
      (-1:F)^(S.filter (fun v => i<v ∧ v<j)).card * A i j *
        supportedPfaffian ((S.erase i).erase j)
          (fun u v => A u v - A i u*A j v/A i j + A j u*A i v/A i j) := by
  have h := supportedPfaffian_partialSourceShear S A j (S.erase j)
    (pivotShearCoefficient A i j) hj (fun _ hx => hx) hskew hdiag
  rw [partialSourceShear_active_congr] at h
  rw [← h]
  exact supportedPfaffian_pivotIsolated S A i j hi hj hij hmin hskew hp

namespace PfaffianElimination
variable [DecidableEq F] {n : ℕ}

/-- On ordered active vertices, the actual field-arithmetic program evaluates
exactly the literal supported signed pairing sum. -/
theorem evaluate_eq_supportedPfaffian (A : Matrix (Fin n) (Fin n) F)
    (active : List (Fin n)) (hskew : ∀ u v, A v u = -A u v)
    (hdiag : ∀ u, A u u=0) (hordered : active.Pairwise (· < ·)) :
    evaluate A active = supportedPfaffian active.toFinset A := by
  let Inv := fun (B : Matrix (Fin n) (Fin n) F) (xs : List (Fin n)) =>
    (∀ u v, B v u = -B u v) ∧ (∀ u, B u u=0) ∧ xs.Pairwise (· < ·)
  apply evaluate_eq_of_pivot_recurrence
    (fun B xs => supportedPfaffian xs.toFinset B) Inv
  · intro B _
    simp
  · intro B i xs hB hz
    apply supportedPfaffian_zero_row _ B i (by simp)
    · intro v hv
      rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | hv
      · exact le_refl _
      · exact ((List.pairwise_cons.mp hB.2.2).1 v hv).le
    · intro j hj hij
      rcases List.mem_cons.mp (List.mem_toFinset.mp hj) with rfl | hj
      · exact (lt_irrefl _ hij).elim
      · exact hz j hj
  · intro B i xs k j hB hp
    have hj : j∈xs := List.mem_of_getElem? (firstPivot_some_spec B i xs hp).2.1
    have hij := (List.pairwise_cons.mp hB.2.2).1 j hj
    have hmin : ∀ v∈(i::xs).toFinset, i≤v := by
      intro v hv
      rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | hv
      · exact le_refl _
      · exact ((List.pairwise_cons.mp hB.2.2).1 v hv).le
    have h := supportedPfaffian_pivot (i::xs).toFinset B i j (by simp) (by simp [hj])
      hij hmin hB.1 hB.2.1 (firstPivot_nonzero B i xs hp)
    rw [firstPivot_between_card B i xs hB.2.2 hp] at h
    rw [← firstPivot_remaining_toFinset B i xs hB.2.2 hp] at h
    exact h
  · intro B i xs k j hB _
    exact ⟨pivotUpdate_skew B i j hB.1, pivotUpdate_diag B i j hB.2.1,
      sorted_eraseIdx hB.2.2 k⟩
  · exact ⟨hskew,hdiag,hordered⟩

/-- The full evaluator computes the literal matching-Pfaffian expansion. -/
theorem evaluate_eq_pairingPfaffian (A : Matrix (Fin n) (Fin n) F)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u=0) :
    evaluate A (List.finRange n) = pairingPfaffian A := by
  rw [evaluate_eq_supportedPfaffian A _ hskew hdiag, List.toFinset_finRange, supportedPfaffian_univ]
  simpa only [List.ofFn_id] using
    (List.pairwise_ofFn.mpr (fun {_ _ : Fin n} h => h) : (List.ofFn id).Pairwise (· < ·))

end PfaffianElimination
end PlanarHom.MultiGraph
