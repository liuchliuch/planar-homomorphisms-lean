import PlanarHom.OccurrenceMatchings

/-!
# Occurrence-aware skew matrices

Each edge label contributes independently to the matrix, so parallel occurrences
are added rather than identified. A Boolean orientation chooses whether the
stored source-to-target direction is positive. Loops cancel, including over rings
of characteristic two. No planarity or Pfaffian-orientation assertion is made.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph

variable {V E R : Type*} [CommRing R]

/-- `true` keeps the stored direction and `false` reverses it. -/
def orientationSign (orientation : E → Bool) (e : E) : R :=
  if orientation e then 1 else -1

@[simp] theorem orientationSign_true (e : E) :
    orientationSign (R := R) (fun _ : E => true) e = 1 := rfl

@[simp] theorem orientationSign_false (e : E) :
    orientationSign (R := R) (fun _ : E => false) e = -1 := rfl

theorem orientationSign_eq_one_or_neg_one (orientation : E → Bool) (e : E) :
    orientationSign (R := R) orientation e = 1 ∨
      orientationSign (R := R) orientation e = -1 := by
  unfold orientationSign
  split_ifs <;> simp

@[simp] theorem orientationSign_sq (orientation : E → Bool) (e : E) :
    orientationSign (R := R) orientation e ^ 2 = 1 := by
  unfold orientationSign
  split_ifs <;> ring

/-- The skew contribution of one labelled occurrence. -/
def occurrenceEntry (G : MultiGraph V E) (orientation : E → Bool) (w : E → R)
    (e : E) (u v : V) : R :=
  (if G.src e = u ∧ G.dst e = v then orientationSign orientation e * w e else 0) -
    (if G.src e = v ∧ G.dst e = u then orientationSign orientation e * w e else 0)

/-- All occurrences are summed, preserving parallel-edge multiplicity. -/
def occurrenceSkewMatrix [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) : Matrix V V R :=
  fun u v => ∑ e, G.occurrenceEntry orientation w e u v

@[simp] theorem occurrenceEntry_diag (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (e : E) (v : V) :
    G.occurrenceEntry orientation w e v v = 0 := by
  simp [occurrenceEntry]

theorem occurrenceEntry_swap (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (e : E) (u v : V) :
    G.occurrenceEntry orientation w e v u = -G.occurrenceEntry orientation w e u v := by
  simp only [occurrenceEntry, neg_sub]

@[simp] theorem occurrenceEntry_loop (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (e : E)
    (he : G.src e = G.dst e) (u v : V) :
    G.occurrenceEntry orientation w e u v = 0 := by
  simp [occurrenceEntry, he, and_comm]

@[simp] theorem occurrenceSkewMatrix_diag [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (v : V) :
    G.occurrenceSkewMatrix orientation w v v = 0 := by
  simp [occurrenceSkewMatrix]

/-- Skew symmetry does not require two to be invertible. -/
theorem occurrenceSkewMatrix_swap [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (u v : V) :
    G.occurrenceSkewMatrix orientation w v u =
      -G.occurrenceSkewMatrix orientation w u v := by
  simp only [occurrenceSkewMatrix]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun e _ => G.occurrenceEntry_swap orientation w e u v)

theorem occurrenceSkewMatrix_transpose [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) :
    (G.occurrenceSkewMatrix orientation w).transpose =
      -G.occurrenceSkewMatrix orientation w := by
  ext u v
  exact G.occurrenceSkewMatrix_swap orientation w u v

/-- Changing any loop weights has no effect on the matrix. -/
theorem occurrenceSkewMatrix_congr_nonloop [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w w' : E → R)
    (hw : ∀ e, G.src e ≠ G.dst e → w e = w' e) :
    G.occurrenceSkewMatrix orientation w = G.occurrenceSkewMatrix orientation w' := by
  ext u v
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.src e = G.dst e
  · simp [G.occurrenceEntry_loop orientation w e he,
      G.occurrenceEntry_loop orientation w' e he]
  · simp only [occurrenceEntry, hw e he]

/-- Setting every loop weight to zero leaves the occurrence matrix unchanged. -/
theorem occurrenceSkewMatrix_erase_loops [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) :
    G.occurrenceSkewMatrix orientation
        (fun e => if G.src e = G.dst e then 0 else w e) =
      G.occurrenceSkewMatrix orientation w := by
  apply G.occurrenceSkewMatrix_congr_nonloop
  intro e he
  simp [he]

/-- The two directed fibers are literal sums over occurrence labels. -/
theorem occurrenceSkewMatrix_eq_forward_sub_reverse [Fintype E]
    (G : MultiGraph V E) (orientation : E → Bool) (w : E → R) (u v : V) :
    G.occurrenceSkewMatrix orientation w u v =
      (∑ e ∈ Finset.univ.filter (fun e => G.src e = u ∧ G.dst e = v),
        orientationSign orientation e * w e) -
      (∑ e ∈ Finset.univ.filter (fun e => G.src e = v ∧ G.dst e = u),
        orientationSign orientation e * w e) := by
  simp only [occurrenceSkewMatrix, occurrenceEntry, Finset.sum_sub_distrib,
    Finset.sum_filter]

theorem occurrenceEntry_add (G : MultiGraph V E) (orientation : E → Bool)
    (w w' : E → R) (e : E) (u v : V) :
    G.occurrenceEntry orientation (fun e => w e + w' e) e u v =
      G.occurrenceEntry orientation w e u v +
        G.occurrenceEntry orientation w' e u v := by
  unfold occurrenceEntry
  split_ifs <;> ring

/-- Additivity keeps the signed contributions of parallel occurrences explicit. -/
theorem occurrenceSkewMatrix_add [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w w' : E → R) :
    G.occurrenceSkewMatrix orientation (fun e => w e + w' e) =
      G.occurrenceSkewMatrix orientation w + G.occurrenceSkewMatrix orientation w' := by
  ext u v
  simp [occurrenceSkewMatrix, occurrenceEntry_add, Finset.sum_add_distrib]

@[simp] theorem occurrenceSkewMatrix_zero [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) : G.occurrenceSkewMatrix orientation (fun _ => (0 : R)) = 0 := by
  ext u v
  simp [occurrenceSkewMatrix, occurrenceEntry]

/-- A single supported occurrence contributes exactly its own skew matrix. -/
theorem occurrenceSkewMatrix_single [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (e : E) (a : R) (u v : V) :
    G.occurrenceSkewMatrix orientation (fun d => if d = e then a else 0) u v =
      G.occurrenceEntry orientation (fun _ => a) e u v := by
  unfold occurrenceSkewMatrix
  rw [Finset.sum_eq_single e]
  · simp [occurrenceEntry]
  · intro d _ hde
    simp [occurrenceEntry, hde]
  · simp

section Ordered
variable [LinearOrder V]

/-- The canonical unordered endpoint pair, written in increasing order. -/
def canonicalPair (G : MultiGraph V E) (e : E) : V × V :=
  (min (G.src e) (G.dst e), max (G.src e) (G.dst e))

/-- The sign of an occurrence when its endpoints are written in increasing order.
Loops may have either sign here, but they never belong to a strict upper fiber. -/
def canonicalSign (G : MultiGraph V E) (orientation : E → Bool) (e : E) : R :=
  if G.src e < G.dst e then orientationSign orientation e else -orientationSign orientation e

theorem canonicalSign_eq_one_or_neg_one (G : MultiGraph V E)
    (orientation : E → Bool) (e : E) :
    G.canonicalSign (R := R) orientation e = 1 ∨
      G.canonicalSign (R := R) orientation e = -1 := by
  unfold canonicalSign orientationSign
  split_ifs <;> simp

@[simp] theorem canonicalSign_sq (G : MultiGraph V E)
    (orientation : E → Bool) (e : E) :
    G.canonicalSign (R := R) orientation e ^ 2 = 1 := by
  unfold canonicalSign
  split_ifs <;> simp

/-- A strict upper endpoint pair records either stored direction. -/
theorem canonicalPair_eq_iff (G : MultiGraph V E) (e : E) {u v : V} (huv : u < v) :
    G.canonicalPair e = (u, v) ↔
      (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u) := by
  constructor
  · intro h
    by_cases he : G.src e ≤ G.dst e
    · left
      simpa [canonicalPair, min_eq_left he, max_eq_right he] using h
    · right
      have he' := le_of_lt (lt_of_not_ge he)
      have hp : G.dst e = u ∧ G.src e = v := by
        simpa [canonicalPair, min_eq_right he', max_eq_left he'] using h
      exact ⟨hp.2, hp.1⟩
  · rintro (⟨hs, ht⟩ | ⟨hs, ht⟩)
    · simp [canonicalPair, hs, ht, min_eq_left huv.le, max_eq_right huv.le]
    · simp [canonicalPair, hs, ht, min_eq_right huv.le, max_eq_left huv.le]

theorem canonicalPair_strict_iff (G : MultiGraph V E) (e : E) :
    (G.canonicalPair e).1 < (G.canonicalPair e).2 ↔ G.src e ≠ G.dst e := by
  simp [canonicalPair, ne_comm]

/-- Canonicalization preserves both endpoint incidences, including both ends of a loop. -/
theorem canonicalPair_incidence (G : MultiGraph V E) (e : E) (v : V) :
    ((if (G.canonicalPair e).1 = v then 1 else 0) +
        (if (G.canonicalPair e).2 = v then 1 else 0) : ℕ) =
      (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) := by
  by_cases he : G.src e ≤ G.dst e
  · simp [canonicalPair, min_eq_left he, max_eq_right he]
  · have he' := le_of_lt (lt_of_not_ge he)
    simp [canonicalPair, min_eq_right he', max_eq_left he', add_comm]

/-- A literal occurrence fiber: parallel labels are distinct inhabitants. -/
abbrev upperFiber (G : MultiGraph V E) (u v : V) :=
  {e : E // G.canonicalPair e = (u, v)}

/-- The signed sum in an upper endpoint fiber, ready for product-of-sums expansion. -/
def upperFiberCoefficient [Fintype E] (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (u v : V) : R :=
  ∑ e : G.upperFiber u v, G.canonicalSign orientation e.val * w e.val

/-- At a strict upper entry, an occurrence contributes precisely its canonical sign. -/
theorem occurrenceEntry_eq_canonical (G : MultiGraph V E)
    (orientation : E → Bool) (w : E → R) (e : E) {u v : V} (huv : u < v) :
    G.occurrenceEntry orientation w e u v =
      if G.canonicalPair e = (u, v) then G.canonicalSign orientation e * w e else 0 := by
  by_cases hf : G.src e = u ∧ G.dst e = v
  · have hp := (G.canonicalPair_eq_iff e huv).2 (Or.inl hf)
    simp [occurrenceEntry, hp, canonicalSign, hf.1, hf.2, huv, huv.ne, huv.ne']
  · by_cases hr : G.src e = v ∧ G.dst e = u
    · have hp := (G.canonicalPair_eq_iff e huv).2 (Or.inr hr)
      simp [occurrenceEntry, hp, canonicalSign, hr.1, hr.2,
        not_lt_of_ge huv.le, huv.ne, huv.ne']
    · have hp : G.canonicalPair e ≠ (u, v) := by
        intro h
        exact (G.canonicalPair_eq_iff e huv).1 h |>.elim hf hr
      simp [occurrenceEntry, hf, hr, hp]

/-- The occurrence matrix entry is exactly the sum over all labels in its fiber. -/
theorem occurrenceSkewMatrix_eq_upperFiberCoefficient [Fintype E]
    (G : MultiGraph V E) (orientation : E → Bool) (w : E → R)
    {u v : V} (huv : u < v) :
    G.occurrenceSkewMatrix orientation w u v = G.upperFiberCoefficient orientation w u v := by
  simp only [occurrenceSkewMatrix, G.occurrenceEntry_eq_canonical orientation w _ huv]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end Ordered
end PlanarHom.MultiGraph
