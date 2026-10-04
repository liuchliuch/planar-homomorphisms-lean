import PlanarHom.OccurrencePfaffianPairings

/-!
# Crossing signs in the least-vertex Pfaffian expansion

These identities compute signs from the literal crossing count. No orientation
or sign-consistency certificate is assumed.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

/-- Express the crossing count as a sum of the outgoing crossings of each pair. -/
theorem pairingCrossings_eq_sum (P : Finset (V × V)) :
    pairingCrossings P = ∑ p ∈ P,
      (P.filter fun q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2).card := by
  simp only [pairingCrossings, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

/-- Inserting the pair at the least endpoint introduces only its outgoing
crossings; all old crossing pairs are retained verbatim. -/
theorem pairingCrossings_insert_least (Q : Finset (V × V)) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1) :
    pairingCrossings (insert (i, j) Q) = pairingCrossings Q +
      (Q.filter fun q => q.1 < j ∧ j < q.2).card := by
  have hnot : (i,j) ∉ Q := by
    intro h
    exact (lt_irrefl i) (hleast (i,j) h)
  rw [pairingCrossings_eq_sum, Finset.sum_insert hnot]
  have hnew : ((insert (i,j) Q).filter
      fun q => i < q.1 ∧ q.1 < j ∧ j < q.2) =
      Q.filter (fun q => q.1 < j ∧ j < q.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hq | hq, ha, hb, hc⟩
      · rcases hq with ⟨rfl, rfl⟩
        exact (lt_irrefl i ha).elim
      · exact ⟨hq, hb, hc⟩
    · rintro ⟨hq, hb, hc⟩
      exact ⟨Or.inr hq, hleast q hq, hb, hc⟩
  have hold (p : V × V) (hp : p ∈ Q) :
      ((insert (i,j) Q).filter
        fun q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) =
      Q.filter (fun q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) := by
    rw [Finset.filter_insert]
    simp [not_lt_of_ge (hleast p hp).le]
  rw [hnew, Finset.sum_congr rfl (fun p hp => congrArg Finset.card (hold p hp))]
  rw [← pairingCrossings_eq_sum]
  exact Nat.add_comm _ _

/-- The multiplicative insertion law for the actual integer crossing sign. -/
theorem pairingSign_insert_least (Q : Finset (V × V)) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1) :
    pairingSign (insert (i, j) Q) =
      (-1 : ℤ) ^ (Q.filter fun q => q.1 < j ∧ j < q.2).card * pairingSign Q := by
  rw [pairingSign, pairingCrossings_insert_least Q i j hleast, pow_add]
  exact mul_comm _ _

/-- Every wholly enclosed pair contributes two endpoints and every crossing
pair contributes one. This equality is over natural numbers, before taking
parity. -/
theorem pairing_interval_incidence (Q : Finset (V × V)) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q, q.2 ≠ j) :
    (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) =
      2 * (Q.filter fun q => q.2 < j).card +
        (Q.filter fun q => q.1 < j ∧ j < q.2).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hi₁ := hleast q hq
  have hi₂ := hi₁.trans (hordered q hq)
  rcases lt_or_gt_of_ne (havoid q hq) with hright | hright
  · have hleft := (hordered q hq).trans hright
    simp [hi₁, hi₂, hleft, hright, not_lt_of_gt hright]
  · by_cases hleft : q.1 < j
    · simp [hi₁, hi₂, hleft, hright, not_lt_of_gt hright]
    · simp [hi₁, hi₂, hleft, hright, not_lt_of_gt hright]

/-- The actual crossing sign agrees with the interval-incidence parity. -/
theorem pairing_crossing_sign_eq_interval_sign (Q : Finset (V × V)) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q, q.2 ≠ j) :
    (-1 : ℤ) ^ (Q.filter fun q => q.1 < j ∧ j < q.2).card =
      (-1 : ℤ) ^ (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
        (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) := by
  rw [pairing_interval_incidence Q i j hleast hordered havoid, pow_add, pow_mul]
  norm_num

/-- A least-vertex insertion sign, with its exponent obtained by ordinary
endpoint incidence counting. For a pairing on an active set, the incidence
hypothesis is its degree-one law summed over the vertices strictly between
`i` and `j`. -/
theorem pairingSign_insert_least_of_incidence (Q : Finset (V × V)) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q, q.2 ≠ j) (k : ℕ)
    (hincidence : (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) = k) :
    pairingSign (insert (i, j) Q) = (-1 : ℤ) ^ k * pairingSign Q := by
  rw [pairingSign_insert_least Q i j hleast,
    pairing_crossing_sign_eq_interval_sign Q i j hleast hordered havoid,
    hincidence]

/-- Double-counting endpoint incidence over a finite interval. Only endpoints
of the selected pairs must lie in the ambient active set. -/
theorem pairing_interval_incidence_eq_sum_degree (Q : Finset (V × V))
    (S : Finset V) (i j : V)
    (hsupport : ∀ q ∈ Q, q.1 ∈ S ∧ q.2 ∈ S) :
    (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) =
    ∑ v ∈ S.filter (fun v => i < v ∧ v < j), (pairGraph V).selectedDegree Q v := by
  letI : DecidableEq V := Classical.decEq V
  simp only [selectedDegree_eq_sum_endpointCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [endpointCount, pairGraph, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq _ q.1 (fun _ => (1 : ℕ)),
    Finset.sum_ite_eq _ q.2 (fun _ => (1 : ℕ))]
  simp [(hsupport q hq).1, (hsupport q hq).2]

/-- Degree one at every active vertex strictly inside the interval turns
endpoint incidence into the interval cardinality. No global matching structure
is needed for this double-counting step. -/
theorem pairing_interval_incidence_eq_card (Q : Finset (V × V))
    (S : Finset V) (i j : V)
    (hsupport : ∀ q ∈ Q, q.1 ∈ S ∧ q.2 ∈ S)
    (hdegree : ∀ v ∈ S, i < v → v < j → (pairGraph V).selectedDegree Q v = 1) :
    (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) =
      (S.filter fun v => i < v ∧ v < j).card := by
  rw [pairing_interval_incidence_eq_sum_degree Q S i j hsupport,
    Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hv, hi, hj⟩ := Finset.mem_filter.mp hv
  exact hdegree v hv hi hj

/-- Full interval-cardinality form of the least-vertex insertion law. The
hypotheses are just support, order, endpoint avoidance, and ordinary degree one. -/
theorem pairingSign_insert_least_of_degree (Q : Finset (V × V))
    (S : Finset V) (i j : V)
    (hleast : ∀ q ∈ Q, i < q.1)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q, q.2 ≠ j)
    (hsupport : ∀ q ∈ Q, q.1 ∈ S ∧ q.2 ∈ S)
    (hdegree : ∀ v ∈ S, i < v → v < j → (pairGraph V).selectedDegree Q v = 1) :
    pairingSign (insert (i, j) Q) =
      (-1 : ℤ) ^ (S.filter fun v => i < v ∧ v < j).card * pairingSign Q := by
  exact pairingSign_insert_least_of_incidence Q i j hleast hordered havoid _
    (pairing_interval_incidence_eq_card Q S i j hsupport hdegree)

/-- General insertion changes the crossing count by incoming and outgoing
crossings of the inserted pair. No least-endpoint hypothesis is required. -/
theorem pairingCrossings_insert (Q : Finset (V × V)) (i j : V)
    (hnot : (i,j) ∉ Q) :
    pairingCrossings (insert (i, j) Q) = pairingCrossings Q +
      (Q.filter fun q => i < q.1 ∧ q.1 < j ∧ j < q.2).card +
      (Q.filter fun q => q.1 < i ∧ i < q.2 ∧ q.2 < j).card := by
  rw [pairingCrossings_eq_sum, Finset.sum_insert hnot]
  have hnew : ((insert (i,j) Q).filter
      fun q => i < q.1 ∧ q.1 < j ∧ j < q.2) =
      Q.filter (fun q => i < q.1 ∧ q.1 < j ∧ j < q.2) := by
    rw [Finset.filter_insert]
    simp
  have hold (p : V × V) :
      ((insert (i,j) Q).filter
        fun q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2).card =
      (Q.filter (fun q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)).card +
        (if p.1 < i ∧ i < p.2 ∧ p.2 < j then 1 else 0) := by
    rw [Finset.filter_insert]
    by_cases h : p.1 < i ∧ i < p.2 ∧ p.2 < j
    · simp [h, Finset.card_insert_of_notMem, Finset.mem_filter, hnot]
    · simp [h]
  rw [hnew]
  simp_rw [hold]
  rw [Finset.sum_add_distrib, ← pairingCrossings_eq_sum]
  have hsum : (∑ p ∈ Q, if p.1 < i ∧ i < p.2 ∧ p.2 < j then 1 else 0) =
      (Q.filter fun q => q.1 < i ∧ i < q.2 ∧ q.2 < j).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum]
  omega

/-- Multiplicative crossing-sign insertion at arbitrary distinct endpoints. -/
theorem pairingSign_insert (Q : Finset (V × V)) (i j : V)
    (hnot : (i,j) ∉ Q) :
    pairingSign (insert (i, j) Q) =
      (-1 : ℤ) ^ ((Q.filter fun q => i < q.1 ∧ q.1 < j ∧ j < q.2).card +
        (Q.filter fun q => q.1 < i ∧ i < q.2 ∧ q.2 < j).card) * pairingSign Q := by
  rw [pairingSign, pairingCrossings_insert Q i j hnot, Nat.add_assoc, pow_add]
  exact mul_comm _ _

/-- At arbitrary endpoints, interval incidence is twice the number of
strictly enclosed pairs plus the two kinds of crossing. Endpoint avoidance is
required only at the first endpoint against `i` and the second against `j`. -/
theorem pairing_interval_incidence_general (Q : Finset (V × V)) (i j : V)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid_i : ∀ q ∈ Q, q.1 ≠ i)
    (havoid_j : ∀ q ∈ Q, q.2 ≠ j) :
    (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) =
      2 * (Q.filter fun q => i < q.1 ∧ q.2 < j).card +
        ((Q.filter fun q => i < q.1 ∧ q.1 < j ∧ j < q.2).card +
        (Q.filter fun q => q.1 < i ∧ i < q.2 ∧ q.2 < j).card) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rcases lt_or_gt_of_ne (havoid_i q hq) with hui | hiu
  · simp [hui, not_lt_of_gt hui]
  · have hiv := hiu.trans (hordered q hq)
    rcases lt_or_gt_of_ne (havoid_j q hq) with hvj | hjv
    · have huj := (hordered q hq).trans hvj
      simp [hiu, hiv, huj, hvj, not_lt_of_gt hiu, not_lt_of_gt hvj]
    · by_cases huj : q.1 < j
      · simp [hiu, hiv, huj, hjv, not_lt_of_gt hiu, not_lt_of_gt hjv]
      · simp [hiu, hiv, huj, hjv, not_lt_of_gt hiu, not_lt_of_gt hjv]

/-- Interval incidence computes the actual arbitrary-pair insertion sign. -/
theorem pairingSign_insert_of_incidence (Q : Finset (V × V)) (i j : V)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid_i : ∀ q ∈ Q, q.1 ≠ i)
    (havoid_j : ∀ q ∈ Q, q.2 ≠ j) (k : ℕ)
    (hincidence : (∑ q ∈ Q, ((if i < q.1 ∧ q.1 < j then 1 else 0) +
      (if i < q.2 ∧ q.2 < j then 1 else 0) : ℕ)) = k) :
    pairingSign (insert (i, j) Q) = (-1 : ℤ) ^ k * pairingSign Q := by
  have hnot : (i,j) ∉ Q := fun h => havoid_i (i,j) h rfl
  rw [pairingSign_insert Q i j hnot, ← hincidence,
    pairing_interval_incidence_general Q i j hordered havoid_i havoid_j]
  simp [pow_add, pow_mul]

/-- Full interval-cardinality insertion sign without a least-endpoint
hypothesis. This is the sign used in an arbitrary-row Pfaffian expansion. -/
theorem pairingSign_insert_of_degree (Q : Finset (V × V))
    (S : Finset V) (i j : V)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid_i : ∀ q ∈ Q, q.1 ≠ i)
    (havoid_j : ∀ q ∈ Q, q.2 ≠ j)
    (hsupport : ∀ q ∈ Q, q.1 ∈ S ∧ q.2 ∈ S)
    (hdegree : ∀ v ∈ S, i < v → v < j → (pairGraph V).selectedDegree Q v = 1) :
    pairingSign (insert (i, j) Q) =
      (-1 : ℤ) ^ (S.filter fun v => i < v ∧ v < j).card * pairingSign Q := by
  exact pairingSign_insert_of_incidence Q i j hordered havoid_i havoid_j _
    (pairing_interval_incidence_eq_card Q S i j hsupport hdegree)

end PlanarHom.MultiGraph
