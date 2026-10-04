import PlanarHom.BlockPfaffianDeterminant

/-! NEW: the identity block is the skew matrix of a literal unique matching.
Its Pfaffian is therefore a sign, including in order zero. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BlockPfaffian
open MultiGraph
attribute [-simp] Fin.natAdd_eq_addNat
variable {R : Type*} [CommRing R] {n : ℕ}

def identityGraph (n : ℕ) : MultiGraph (Fin (n+n)) (Fin n) :=
  ⟨Fin.castAdd n, Fin.natAdd n⟩

theorem identityGraph_matching_iff (M : Finset (Fin n)) :
    (identityGraph n).PerfectMatching M ↔ M = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    have hh := h (i.castAdd n)
    simp only [selectedDegree, identityGraph, Fin.castAdd_inj, right_ne_left,
      if_false, add_zero] at hh
    by_contra hn
    simp [hn] at hh
  · rintro rfl v
    induction v using Fin.addCases <;>
      simp [identityGraph, selectedDegree]

theorem identityGraph_skew :
    (identityGraph n).occurrenceSkewMatrix (fun _ => true) (fun _ => (1:R)) =
      block (1 : Matrix (Fin n) (Fin n) R) := by
  have hf (i j : Fin n) :
      (Finset.univ.filter (fun e => e = i ∧ e = j)) =
        (if i = j then {i} else ∅) := by
    split_ifs with h
    · subst j; ext e; simp
    · ext e; simp; aesop
  ext u v
  induction u using Fin.addCases <;> induction v using Fin.addCases
  all_goals simp [occurrenceSkewMatrix, occurrenceEntry, identityGraph, Matrix.one_apply, hf]
  all_goals split_ifs <;> simp


theorem pairingPfaffian_identityBlock :
    pairingPfaffian (block (1 : Matrix (Fin n) (Fin n) R)) =
      (identityGraph n).matchingPfaffianSign (R := R) (fun _ => true) Finset.univ := by
  rw [← identityGraph_skew, pairingPfaffian_occurrenceSkewMatrix]
  let M₀ : {M : Finset (Fin n) // (identityGraph n).PerfectMatching M} :=
    ⟨Finset.univ, identityGraph_matching_iff _ |>.mpr rfl⟩
  have hm : ∀ M : {M : Finset (Fin n) // (identityGraph n).PerfectMatching M}, M = M₀ := by
    intro M
    apply Subtype.ext
    exact (identityGraph_matching_iff M.val).mp M.property
  rw [Finset.sum_eq_single M₀]
  · simp [M₀]
  · intro M _ hne
    exact (hne (hm M)).elim
  · simp

theorem identityBlock_sq :
    pairingPfaffian (block (1 : Matrix (Fin n) (Fin n) R)) ^ 2 = 1 := by
  rw [pairingPfaffian_identityBlock]
  exact matchingPfaffianSign_sq _ _ _

/-- The calibration is an actual sign, not a nonvanishing hypothesis. -/
theorem determinant_eq_calibrated_pfaffian (A : Matrix (Fin n) (Fin n) R) :
    A.det = pairingPfaffian (block (1 : Matrix (Fin n) (Fin n) R)) *
      pairingPfaffian (block A) := by
  rw [pairingPfaffian_block A, ← mul_assoc, ← pow_two, identityBlock_sq, one_mul]

attribute [simp] Fin.natAdd_eq_addNat

end PlanarHom.BlockPfaffian
