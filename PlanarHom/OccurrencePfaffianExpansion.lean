import PlanarHom.OccurrencePfaffianExpansionSigns

/-!
# NEW reconstruction: supported pairing Pfaffian recurrence
The missing prefix has been newly proved from literal endpoint incidence.
The final recurrence proofs retain the recovered original tail with explicit
compatibility repairs only. This is not a recovered complete original file.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

/-- A strict ordered pairing whose endpoint degrees are the indicator of `S`. -/
def PairingOn (S : Finset V) (P : Finset (V × V)) : Prop :=
  (∀ v, (pairGraph V).selectedDegree P v = if v ∈ S then 1 else 0) ∧
    ∀ p ∈ P, p.1 < p.2

/-- The actual signed pairing expression on an active vertex set. -/
def supportedPfaffian [Fintype V] {R : Type*} [CommRing R]
    (S : Finset V) (A : Matrix V V R) : R :=
  ∑ P : {P : Finset (V × V) // PairingOn S P},
    (pairingSign P.val : R) * ∏ p ∈ P.val, A p.1 p.2

@[simp] theorem pairingOn_univ [Fintype V] (P : Finset (V × V)) :
    PairingOn Finset.univ P ↔ IsPairing P := by
  simp only [PairingOn, IsPairing, PerfectMatching, Finset.mem_univ, if_true]

@[simp] theorem supportedPfaffian_univ [Fintype V] {R : Type*} [CommRing R]
    (A : Matrix V V R) : supportedPfaffian Finset.univ A = pairingPfaffian A := by
  unfold supportedPfaffian pairingPfaffian
  apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun P => pairingOn_univ P))
  intro P
  rfl

theorem PairingOn.endpoints_mem {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {p : V × V} (hp : p ∈ P) : p.1 ∈ S ∧ p.2 ∈ S := by
  have hle (v : V) := Finset.single_le_sum
    (fun q (_ : q ∈ P) => Nat.zero_le ((pairGraph V).endpointCount q v)) hp
  have hsum (v : V) : (∑ q ∈ P, (pairGraph V).endpointCount q v) =
      if v ∈ S then 1 else 0 := hP.1 v
  constructor
  · by_contra hn
    have h := hle p.1
    rw [hsum, if_neg hn] at h
    simp [endpointCount, pairGraph] at h
  · by_contra hn
    have h := hle p.2
    rw [hsum, if_neg hn] at h
    simp [endpointCount, pairGraph] at h

theorem PairingOn.pair_notMem {S : Finset V} {Q : Finset (V × V)} {i j : V}
    (hQ : PairingOn ((S.erase i).erase j) Q) : (i,j) ∉ Q := by
  intro hp
  have h := (hQ.endpoints_mem hp).1
  simp at h

theorem PairingOn.exists_min_pair {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) (hmin : ∀ v ∈ S, i ≤ v) :
    ∃ j, i < j ∧ (i,j) ∈ P := by
  have hs : 0 < ∑ q ∈ P, (pairGraph V).endpointCount q i := by
    change 0 < (pairGraph V).selectedDegree P i
    rw [hP.1, if_pos hi]
    exact Nat.zero_lt_one
  obtain ⟨p, hp, hpos⟩ := Finset.sum_pos_iff.mp hs
  have he : p.1 = i ∨ p.2 = i := by
    by_contra hn
    push_neg at hn
    simp [endpointCount, pairGraph, hn.1, hn.2] at hpos
  rcases he with he | he
  · refine ⟨p.2, he ▸ hP.2 p hp, ?_⟩
    simpa only [← he, Prod.mk.eta] using hp
  · have hle := hmin p.1 (hP.endpoints_mem hp).1
    have hlt := hP.2 p hp
    rw [he] at hlt
    exact (not_lt_of_ge hle hlt).elim

/-- Removing a selected pair removes precisely its two endpoint incidences. -/
theorem PairingOn.erase_pair {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hp : (i,j) ∈ P) :
    PairingOn ((S.erase i).erase j) (P.erase (i,j)) := by
  have hij : i < j := hP.2 (i,j) hp
  have hi := (hP.endpoints_mem hp).1
  have hj := (hP.endpoints_mem hp).2
  refine ⟨?_, fun p hp => hP.2 p (Finset.mem_of_mem_erase hp)⟩
  intro v
  have hd := hP.1 v
  change (∑ q ∈ P, (pairGraph V).endpointCount q v) = _ at hd
  rw [← Finset.sum_erase_add _ _ hp] at hd
  change (∑ q ∈ P.erase (i,j), (pairGraph V).endpointCount q v) = _
  by_cases hv : v = i
  · subst v
    simp [endpointCount, pairGraph, hi, hij.ne'] at hd ⊢
    omega
  · by_cases hw : v = j
    · subst v
      simp [endpointCount, pairGraph, hj, hij.ne] at hd ⊢
      omega
    · simpa [endpointCount, pairGraph, hv, hw, Ne.symm hv, Ne.symm hw] using hd

/-- Conversely, insertion restores the two removed endpoint incidences. -/
theorem PairingOn.insert_pair {S : Finset V} {Q : Finset (V × V)} {i j : V}
    (hQ : PairingOn ((S.erase i).erase j) Q) (hi : i ∈ S) (hj : j ∈ S)
    (hij : i < j) : PairingOn S (insert (i,j) Q) := by
  refine ⟨?_, ?_⟩
  · intro v
    change (∑ q ∈ insert (i,j) Q, (pairGraph V).endpointCount q v) = _
    rw [Finset.sum_insert hQ.pair_notMem]
    change (pairGraph V).endpointCount (i,j) v + (pairGraph V).selectedDegree Q v = _
    rw [hQ.1]
    by_cases hv : v = i
    · subst v
      simp [endpointCount, pairGraph, hi, hij.ne']
    · by_cases hw : v = j
      · subst v
        simp [endpointCount, pairGraph, hj, hij.ne]
      · simp [endpointCount, pairGraph, hv, hw, Ne.symm hv, Ne.symm hw]
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hij
    · exact hQ.2 p hp

/-- Decompose a supported pairing at its least active vertex. -/
def pairingOnSplitEquiv (S : Finset V) (i : V) (hi : i ∈ S)
    (hmin : ∀ v ∈ S, i ≤ v) :
    (Σ j : {j : V // j ∈ S ∧ i < j},
      {Q : Finset (V × V) // PairingOn ((S.erase i).erase j.val) Q}) ≃
        {P : Finset (V × V) // PairingOn S P} :=
  Equiv.ofBijective
    (fun a => ⟨insert (i,a.1.val) a.2.val,
      a.2.property.insert_pair hi a.1.property.1 a.1.property.2⟩)
    (by
      constructor
      · rintro ⟨⟨j,hj⟩,⟨Q,hQ⟩⟩ ⟨⟨k,hk⟩,⟨T,hT⟩⟩ heq
        have hh : insert (i,j) Q = insert (i,k) T := congrArg Subtype.val heq
        have hjk : j = k := by
          have hmem : (i,j) ∈ insert (i,k) T := hh ▸ Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp hmem with he | he
          · exact congrArg Prod.snd he
          · have hv := (hT.endpoints_mem he).1
            simp at hv
        subst k
        have hQT : Q = T := by
          have he := congrArg (fun P => P.erase (i,j)) hh
          simpa [hQ.pair_notMem, hT.pair_notMem] using he
        subst T
        rfl
      · intro P
        obtain ⟨j,hij,hp⟩ := P.property.exists_min_pair hi hmin
        refine ⟨⟨⟨j,(P.property.endpoints_mem hp).2,hij⟩,
          ⟨P.val.erase (i,j),P.property.erase_pair hp⟩⟩, ?_⟩
        apply Subtype.ext
        exact Finset.insert_erase hp)

@[simp] theorem pairingOn_empty_iff (P : Finset (V × V)) : PairingOn ∅ P ↔ P = ∅ := by
  constructor
  · intro hP
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact Finset.notMem_empty _ (hP.endpoints_mem hp).1
  · rintro rfl
    simp [PairingOn, selectedDegree]
@[simp] theorem supportedPfaffian_empty [Fintype V] {R : Type*} [CommRing R]
    (A : Matrix V V R) : supportedPfaffian ∅ A = 1 := by
  unfold supportedPfaffian
  rw [sum_subtype_eq_ite (PairingOn ∅)
    (fun P => (pairingSign P : R) * ∏ p ∈ P, A p.1 p.2)]
  simp [pairingSign, pairingCrossings]

/-- The no-pivot branch is mathematically zero, even in the presence of zero or
signed coefficients elsewhere in the matrix. Only the active first row is used. -/
theorem supportedPfaffian_zero_row [Fintype V] {R : Type*} [CommRing R]
    (S : Finset V) (A : Matrix V V R) (i : V) (hi : i ∈ S)
    (hmin : ∀ v ∈ S, i ≤ v)
    (hzero : ∀ j ∈ S, i < j → A i j = 0) : supportedPfaffian S A = 0 := by
  unfold supportedPfaffian
  apply Finset.sum_eq_zero
  intro P _
  obtain ⟨j, hij, hp⟩ := P.property.exists_min_pair hi hmin
  have hj := (P.property.endpoints_mem hp).2
  rw [Finset.prod_eq_zero hp (hzero j hj hij), mul_zero]

/-- Each recursion branch removes exactly two distinct active vertices. -/
theorem erase_pair_card (S : Finset V) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) :
    ((S.erase i).erase j).card + 2 = S.card := by
  have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.ne', hj⟩
  have h1 := Finset.card_erase_add_one hi
  have h2 := Finset.card_erase_add_one hj'
  omega

/-- Inserting the pair from the least active vertex contributes the precise
pivot-position parity. The exponent counts active vertices strictly between the
pivot endpoints, not their absolute ambient indices. -/
theorem PairingOn.sign_insert_min {S : Finset V} {Q : Finset (V × V)} {i j : V}
    (hQ : PairingOn ((S.erase i).erase j) Q) (hmin : ∀ v ∈ S, i ≤ v) :
    pairingSign (insert (i,j) Q) =
      (-1 : ℤ) ^ (S.filter (fun v => i < v ∧ v < j)).card * pairingSign Q := by
  apply pairingSign_insert_least_of_degree Q S i j
  · intro q hq
    have hmem := (hQ.endpoints_mem hq).1
    simp only [Finset.mem_erase] at hmem
    exact lt_of_le_of_ne (hmin q.1 hmem.2.2) (Ne.symm hmem.2.1)
  · exact hQ.2
  · intro q hq
    exact (Finset.mem_erase.mp (hQ.endpoints_mem hq).2).1
  · intro q hq
    have he := hQ.endpoints_mem hq
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he.1),
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he.2)⟩
  · intro v hv hiv hvj
    rw [hQ.1, if_pos]
    simp [hv, hiv.ne', hvj.ne]

/-- Exact signed Laplace expansion of the actual pairing Pfaffian on an active
set. This is a semantic equality, not an assumed recurrence or determinant
surrogate. -/
theorem supportedPfaffian_expand_min [Fintype V] {R : Type*} [CommRing R]
    (S : Finset V) (A : Matrix V V R) (i : V) (hi : i ∈ S)
    (hmin : ∀ v ∈ S, i ≤ v) :
    supportedPfaffian S A =
      ∑ j : {j : V // j ∈ S ∧ i < j},
        (-1 : R) ^ (S.filter (fun v => i < v ∧ v < j.val)).card * A i j.val *
          supportedPfaffian ((S.erase i).erase j.val) A := by
  classical
  let e := pairingOnSplitEquiv S i hi hmin
  calc
    supportedPfaffian S A =
        ∑ a : Σ j : {j : V // j ∈ S ∧ i < j},
          {Q : Finset (V × V) // PairingOn ((S.erase i).erase j.val) Q},
          (pairingSign (insert (i,a.1.val) a.2.val) : R) *
            ∏ p ∈ insert (i,a.1.val) a.2.val, A p.1 p.2 := by
      symm
      apply Fintype.sum_equiv e
      intro a
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      unfold supportedPfaffian
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      rw [Q.property.sign_insert_min hmin, Finset.prod_insert Q.property.pair_notMem]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      ring

/-- The branch sign is the actual permutation parity for moving the selected
partner next to the least active vertex. If every other first-row entry is zero,
only this branch survives; zero values of the selected entry are also allowed. -/
theorem supportedPfaffian_single_pivot_row [Fintype V] {R : Type*} [CommRing R]
    (S : Finset V) (A : Matrix V V R) (i j : V) (hi : i ∈ S) (hj : j ∈ S)
    (hij : i < j) (hmin : ∀ v ∈ S, i ≤ v)
    (hzero : ∀ k ∈ S, i < k → k ≠ j → A i k = 0) :
    supportedPfaffian S A =
      (-1 : R) ^ (S.filter (fun v => i < v ∧ v < j)).card * A i j *
        supportedPfaffian ((S.erase i).erase j) A := by
  rw [supportedPfaffian_expand_min S A i hi hmin]
  let jj : {j : V // j ∈ S ∧ i < j} := ⟨j,hj,hij⟩
  rw [Finset.sum_eq_single jj]
  · intro k _ hkj
    have hk : k.val ≠ j := fun h => hkj (Subtype.ext h)
    rw [hzero k.val k.property.1 k.property.2 hk, mul_zero, zero_mul]
  · simp

/-- A sign-insertion formula available for arbitrary removed pairs, needed for
later simultaneous row/column operations. -/
theorem PairingOn.sign_insert {S : Finset V} {Q : Finset (V × V)} {i j : V}
    (hQ : PairingOn ((S.erase i).erase j) Q) :
    pairingSign (insert (i,j) Q) =
      (-1 : ℤ) ^ (S.filter (fun v => i < v ∧ v < j)).card * pairingSign Q := by
  apply pairingSign_insert_of_degree Q S i j hQ.2
  · intro q hq
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hQ.endpoints_mem hq).1)).1
  · intro q hq
    exact (Finset.mem_erase.mp (hQ.endpoints_mem hq).2).1
  · intro q hq
    have he := hQ.endpoints_mem hq
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he.1),
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he.2)⟩
  · intro v hv hiv hvj
    rw [hQ.1, if_pos]
    simp [hv, hiv.ne', hvj.ne]

end PlanarHom.MultiGraph




