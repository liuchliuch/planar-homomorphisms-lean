import PlanarHom.FisherCubicWeighted

/-! The exact prefix-parity extension used to make arbitrary degrees cubic. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher

/-- Prefix XOR values, including the initial state before the first port. -/
def parityScan : {d : ℕ} → Bool → (Fin d → Bool) → Fin (d + 1) → Bool
  | 0, s, _ => fun _ => s
  | _d + 1, s, a => Fin.cons s (parityScan (Bool.xor s (a 0)) (fun i => a i.succ))

@[simp] theorem parityScan_zero {d : ℕ} (s : Bool) (a : Fin d → Bool) :
    parityScan s a 0 = s := by cases d <;> rfl

theorem parityScan_step {d : ℕ} (s : Bool) (a : Fin d → Bool) (i : Fin d) :
    parityScan s a i.succ = Bool.xor (parityScan s a i.castSucc) (a i) := by
  induction d generalizing s with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parityScan]
    · simpa [parityScan] using ih (Bool.xor s (a 0)) (fun k => a k.succ) j

/-- Every sequence obeying the local parity recurrence is the prefix scan. -/
theorem parityScan_unique {d : ℕ} (s : Bool) (a : Fin d → Bool)
    (q : Fin (d + 1) → Bool) (h0 : q 0 = s)
    (hstep : ∀ i, q i.succ = Bool.xor (q i.castSucc) (a i)) : q = parityScan s a := by
  induction d generalizing s with
  | zero =>
    funext j
    have hj : j = 0 := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    simpa [hj, parityScan] using h0
  | succ d ih =>
    have ht : (fun j : Fin (d + 1) => q j.succ) =
        parityScan (Bool.xor s (a 0)) (fun i => a i.succ) := by
      apply ih
      · simpa only [Fin.castSucc_zero, h0] using hstep 0
      · intro i
        simpa only [Fin.succ_castSucc] using hstep i.succ
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact h0
    · exact congrFun ht k

/-- Ending at zero is equivalent to the parity of the selected input ports. -/
theorem parityScan_last_false_iff {d : ℕ} (s : Bool) (a : Fin d → Bool) :
    parityScan s a (Fin.last d) = false ↔
      (Even (∑ i, (if a i then 1 else 0 : ℕ)) ↔ s = false) := by
  induction d generalizing s with
  | zero => simp [parityScan]
  | succ d ih =>
    change parityScan (Bool.xor s (a 0)) (fun i => a i.succ) (Fin.last d) = false ↔ _
    rw [ih, Fin.sum_univ_succ]
    cases s <;> cases a 0 <;> simp [Nat.even_add, Bool.xor]

theorem parityScan_false_last_iff {d : ℕ} (a : Fin d → Bool) :
    parityScan false a (Fin.last d) = false ↔ Even (∑ i, (if a i then 1 else 0 : ℕ)) := by
  simpa using parityScan_last_false_iff false a

/-- The two boundary edges must be absent; every internal edge is then forced. -/
def ParityPath {d : ℕ} (a : Fin d → Bool) (q : Fin (d + 1) → Bool) : Prop :=
  q 0 = false ∧ q (Fin.last d) = false ∧
    ∀ i, q i.succ = Bool.xor (q i.castSucc) (a i)

theorem parityPath_iff {d : ℕ} (a : Fin d → Bool) (q : Fin (d + 1) → Bool) :
    ParityPath a q ↔
      Even (∑ i, (if a i then 1 else 0 : ℕ)) ∧ q = parityScan false a := by
  constructor
  · rintro ⟨h0, hlast, hstep⟩
    have hq := parityScan_unique false a q h0 hstep
    refine ⟨?_, hq⟩
    exact (parityScan_false_last_iff a).mp (hq ▸ hlast)
  · rintro ⟨heven, rfl⟩
    exact ⟨parityScan_zero _ _, (parityScan_false_last_iff a).mpr heven,
      parityScan_step _ _⟩

end PlanarHom.Fisher
