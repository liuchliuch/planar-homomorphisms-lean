import PlanarHom.OccurrencePfaffianPairings

/-!
# Low-dimensional occurrence Pfaffian regressions

These are exact identities for the signed pairing expansion. They neither
construct a Pfaffian orientation nor assert an efficient evaluation algorithm.
The two-vertex example retains three distinct parallel occurrences, including a
zero and a negative weight, and a loop whose weight has no effect.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph

@[simp] theorem pairingSign_singleton {V : Type*} [LinearOrder V] (p : V × V) :
    pairingSign ({p} : Finset (V × V)) = 1 := by
  simp [pairingSign, pairingCrossings, Finset.filter_singleton]

/-- There is exactly one normalized pairing on two ordered vertices. -/
theorem isPairing_fin_two_iff (P : Finset (Fin 2 × Fin 2)) :
    IsPairing P ↔ P = {(0, 1)} := by
  constructor
  · intro hP
    have hc := hP.1.card_vertices (pairGraph (Fin 2)) P
    have hcard : P.card = 1 := by simpa using hc.symm
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
    have hlt := hP.2 p (Finset.mem_singleton_self _)
    have hp : p = (0, 1) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_zero, Fin.val_one]
      · have := p.1.isLt
        have := p.2.isLt
        exact show p.1.val = 0 by omega
      · have := p.1.isLt
        have := p.2.isLt
        exact show p.2.val = 1 by omega
    rw [hp]
  · rintro rfl
    constructor
    · intro v
      have hv : v = 0 ∨ v = 1 := by omega
      rcases hv with rfl | rfl <;> simp [selectedDegree, pairGraph]
    · simp

/-- The literal pairing expansion has the expected two-dimensional value. -/
@[simp] theorem pairingPfaffian_fin_two {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) : pairingPfaffian A = A 0 1 := by
  let p : {P : Finset (Fin 2 × Fin 2) // IsPairing P} :=
    ⟨{(0, 1)}, (isPairing_fin_two_iff _).2 rfl⟩
  have hp (q : {P : Finset (Fin 2 × Fin 2) // IsPairing P}) : q = p := by
    apply Subtype.ext
    exact (isPairing_fin_two_iff _).1 q.property
  unfold pairingPfaffian
  rw [Finset.sum_eq_single p]
  · simp [p]
  · intro q _ hq
    exact (hq (hp q)).elim
  · simp

namespace PfaffianRegression

/-- Labels `0`, `1`, and `2` are parallel; label `3` is a loop at zero. -/
def parallelAndLoop : MultiGraph (Fin 2) (Fin 4) where
  src := fun _ => 0
  dst := fun e => if e = 3 then 0 else 1

/-- Each nonloop label is independently a genuine perfect matching. -/
theorem singleton_perfect (e : Fin 4) (he : e ≠ 3) :
    parallelAndLoop.PerfectMatching {e} := by
  intro v
  have hv : v = 0 ∨ v = 1 := by omega
  rcases hv with rfl | rfl <;> simp [selectedDegree, parallelAndLoop, he]

/-- Arbitrary weights are summed literally; the loop weight disappears. -/
theorem parallelAndLoop_pfaffian {R : Type*} [CommRing R] (w : Fin 4 → R) :
    pairingPfaffian (parallelAndLoop.occurrenceSkewMatrix (fun _ => true) w) =
      w 0 + w 1 + w 2 := by
  rw [pairingPfaffian_fin_two]
  simp [occurrenceSkewMatrix, occurrenceEntry, parallelAndLoop, Fin.sum_univ_succ]
  ring

/-- Negative and zero weights require no positivity or nonvanishing hypothesis. -/
theorem signed_zero_parallel_pfaffian :
    pairingPfaffian (parallelAndLoop.occurrenceSkewMatrix (fun _ => true)
      ![(3 : ℤ), -5, 0, 100]) = -2 := by
  rw [parallelAndLoop_pfaffian]
  change (3 : ℤ) + -5 + 0 = -2
  norm_num

/-- A loop remains invisible for every possible loop weight. -/
theorem arbitrary_loop_weight (l : ℤ) :
    pairingPfaffian (parallelAndLoop.occurrenceSkewMatrix (fun _ => true)
      ![(3 : ℤ), -5, 0, l]) = -2 := by
  rw [parallelAndLoop_pfaffian]
  change (3 : ℤ) + -5 + 0 = -2
  norm_num

/-- Two positive parallel occurrences cancel under opposite directions.
This is why an arbitrary orientation does not give the unsigned matching sum. -/
theorem opposite_parallel_cancellation :
    pairingPfaffian (parallelAndLoop.occurrenceSkewMatrix (fun e => e != 1)
      ![(1 : ℤ), 1, 0, 0]) = 0 := by
  rw [pairingPfaffian_fin_two]
  norm_num [occurrenceSkewMatrix, occurrenceEntry, parallelAndLoop,
    orientationSign, Fin.sum_univ_succ]
  decide

/-- Keeping those same directions aligned yields their sum. -/
theorem aligned_parallel_addition :
    pairingPfaffian (parallelAndLoop.occurrenceSkewMatrix (fun _ => true)
      ![(1 : ℤ), 1, 0, 0]) = 2 := by
  rw [parallelAndLoop_pfaffian]
  change (1 : ℤ) + 1 + 0 = 2
  norm_num

end PfaffianRegression
end PlanarHom.MultiGraph
