import PlanarHom.OccurrencePfaffianPairExchange

/-! NEW reconstruction: cancellation for repeated rows and elementary shear.
This file is under active verification until its independent audit passes. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

@[simp] theorem orderedEndpointPair_swap (i j : V) :
    orderedEndpointPair j i = orderedEndpointPair i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [orderedEndpointPair,h,not_lt_of_gt h]
  · rfl
  · simp [orderedEndpointPair,h,not_lt_of_gt h]

theorem orderedEndpointPair_incident (i j : V) :
    (orderedEndpointPair i j).1 = i ∨ (orderedEndpointPair i j).2 = i := by
  unfold orderedEndpointPair
  split_ifs <;> simp

theorem orderedEndpointPair_endpoints (i j v : V) :
    ((orderedEndpointPair i j).1 = v ∨ (orderedEndpointPair i j).2 = v) ↔ v = i ∨ v = j := by
  unfold orderedEndpointPair
  split_ifs <;> simp [eq_comm,or_comm]

theorem orderedEndpointPair_right_injective (i : V) :
    Function.Injective (orderedEndpointPair i) := by
  intro a b h
  unfold orderedEndpointPair at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> aesop

theorem PairingOn.eq_of_incident {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {p q : V × V} (hp : p ∈ P) (hq : q ∈ P) {i : V}
    (hip : p.1 = i ∨ p.2 = i) (hiq : q.1 = i ∨ q.2 = i) : p = q := by
  by_contra hne
  have havoid := hP.other_pair_avoids hp (Finset.mem_erase.mpr ⟨Ne.symm hne,hq⟩) hip
  exact hiq.elim havoid.1 havoid.2

/-- The unique partner, returning the input only outside a supported pairing. -/
def pairingPartner (P : Finset (V × V)) (i : V) : V :=
  if h : ∃ j, i ≠ j ∧ orderedEndpointPair i j ∈ P then Classical.choose h else i

theorem PairingOn.partner_exists {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) :
    ∃ j, i ≠ j ∧ orderedEndpointPair i j ∈ P := by
  obtain ⟨⟨a,b⟩,hp,hip⟩ := hP.exists_incident_pair hi
  have hab : a < b := hP.2 (a,b) hp
  rcases hip with rfl | rfl
  · exact ⟨b,hab.ne,by simpa [orderedEndpointPair,hab] using hp⟩
  · exact ⟨a,hab.ne',by simpa [orderedEndpointPair,not_lt_of_gt hab] using hp⟩

theorem PairingOn.partner_spec {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) :
    i ≠ pairingPartner P i ∧ orderedEndpointPair i (pairingPartner P i) ∈ P := by
  unfold pairingPartner
  rw [dif_pos (hP.partner_exists hi)]
  exact Classical.choose_spec (hP.partner_exists hi)

theorem PairingOn.partner_eq_of_mem {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S)
    (hp : orderedEndpointPair i j ∈ P) : pairingPartner P i = j := by
  apply orderedEndpointPair_right_injective i
  exact hP.eq_of_incident (hP.partner_spec hi).2 hp
    (orderedEndpointPair_incident _ _) (orderedEndpointPair_incident _ _)

theorem PairingOn.partner_mem {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) : pairingPartner P i ∈ S := by
  have hm := hP.endpoints_mem (hP.partner_spec hi).2
  unfold orderedEndpointPair at hm
  split_ifs at hm <;> tauto

/-- Removing the canonical pair removes its endpoints in either order. -/
theorem PairingOn.erase_orderedPair {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hp : orderedEndpointPair i j ∈ P) :
    PairingOn ((S.erase i).erase j) (P.erase (orderedEndpointPair i j)) := by
  unfold orderedEndpointPair at hp ⊢
  split_ifs at hp ⊢ with h
  · exact hP.erase_pair hp
  · simpa only [Finset.erase_right_comm] using hP.erase_pair hp

/-- Inserting a normalized pair restores its two distinct endpoints. -/
theorem PairingOn.insert_orderedPair {S : Finset V} {Q : Finset (V × V)} {i j : V}
    (hQ : PairingOn ((S.erase i).erase j) Q) (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    PairingOn S (insert (orderedEndpointPair i j) Q) := by
  unfold orderedEndpointPair
  split_ifs with h
  · exact hQ.insert_pair hi hj h
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    apply PairingOn.insert_pair (i := j) (j := i) ?_ hj hi hji
    simpa only [Finset.erase_right_comm] using hQ



theorem orderedEndpointPair_avoids (i j v : V) :
    ((orderedEndpointPair i j).1 ≠ v ∧ (orderedEndpointPair i j).2 ≠ v) ↔ i ≠ v ∧ j ≠ v := by
  unfold orderedEndpointPair
  split_ifs <;> simp [and_comm]

theorem orderedEndpointPair_ne {i j a b : V} (hji : j ≠ i) (hja : j ≠ a) :
    orderedEndpointPair i a ≠ orderedEndpointPair j b := by
  intro he
  have h := orderedEndpointPair_incident j b
  rw [← he] at h
  exact ((orderedEndpointPair_endpoints i a j).mp h).elim hji hja

/-- The partners of two vertices not matched to each other are all distinct. -/
theorem PairingOn.partners_disjoint {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hne : pairingPartner P i ≠ j) :
    pairingPartner P j ≠ i ∧ pairingPartner P i ≠ pairingPartner P j := by
  have hp := (hP.partner_spec hi).2
  have hq := (hP.partner_spec hj).2
  have hpq : orderedEndpointPair i (pairingPartner P i) ≠
      orderedEndpointPair j (pairingPartner P j) := orderedEndpointPair_ne hij.symm hne.symm
  have hq' := Finset.mem_erase.mpr ⟨hpq.symm,hq⟩
  have hav₁ := hP.other_pair_avoids hp hq' (orderedEndpointPair_incident i (pairingPartner P i))
  have hav₂ := hP.other_pair_avoids hp hq' (i := pairingPartner P i) (by
    rw [orderedEndpointPair_swap]
    exact orderedEndpointPair_incident _ _)
  exact ⟨((orderedEndpointPair_avoids _ _ _).mp hav₁).2,
    ((orderedEndpointPair_avoids _ _ _).mp hav₂).2.symm⟩

/-- Swapping the partners of two active vertices, with their common-pair case fixed. -/
def swapPairingPartners (P : Finset (V × V)) (i j : V) : Finset (V × V) :=
  if pairingPartner P i = j then P else
    insert (orderedEndpointPair i (pairingPartner P j))
      (insert (orderedEndpointPair j (pairingPartner P i))
        ((P.erase (orderedEndpointPair i (pairingPartner P i))).erase
          (orderedEndpointPair j (pairingPartner P j))))

/-- Four-endpoint reconstruction, including the complete residual pairing. -/
theorem PairingOn.partner_decomposition {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hne : pairingPartner P i ≠ j) :
    let a := pairingPartner P i
    let b := pairingPartner P j
    let Q := (P.erase (orderedEndpointPair i a)).erase (orderedEndpointPair j b)
    PairingOn ((((S.erase i).erase a).erase j).erase b) Q ∧
      insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b) Q) = P := by
  dsimp only
  have hp := (hP.partner_spec hi).2
  have hq := (hP.partner_spec hj).2
  have hpq : orderedEndpointPair i (pairingPartner P i) ≠
      orderedEndpointPair j (pairingPartner P j) := orderedEndpointPair_ne hij.symm hne.symm
  have hq' := Finset.mem_erase.mpr ⟨hpq.symm,hq⟩
  exact ⟨(hP.erase_orderedPair hp).erase_orderedPair hq', by
    rw [Finset.insert_erase hq',Finset.insert_erase hp]⟩

/-- The endpoint switch preserves all active degree-one constraints. -/
theorem PairingOn.swap_partners {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    PairingOn S (swapPairingPartners P i j) := by
  unfold swapPairingPartners
  split_ifs with hne
  · exact hP
  · have hia := (hP.partner_spec hi).1
    have hjb := (hP.partner_spec hj).1
    have ha := hP.partner_mem hi
    have hb := hP.partner_mem hj
    obtain ⟨hbi,hab⟩ := hP.partners_disjoint hi hj hij hne
    have hQ := (hP.partner_decomposition hi hj hij hne).1
    apply PairingOn.insert_orderedPair (i := i) (j := pairingPartner P j) ?_ hi hb hbi.symm
    apply PairingOn.insert_orderedPair (i := j) (j := pairingPartner P i) ?_
      (by simp [hj,hij.symm,hjb]) (by simp [ha,hia.symm,hab]) (Ne.symm hne)
    convert hQ using 1
    ext v
    simp only [Finset.mem_erase]
    aesop

/-- Swapped partners are identified by their newly inserted canonical pairs. -/
theorem PairingOn.swap_partner_values {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hne : pairingPartner P i ≠ j) :
    pairingPartner (swapPairingPartners P i j) i = pairingPartner P j ∧
      pairingPartner (swapPairingPartners P i j) j = pairingPartner P i := by
  have hP' := hP.swap_partners hi hj hij
  constructor
  · apply hP'.partner_eq_of_mem hi
    simp [swapPairingPartners,hne]
  · apply hP'.partner_eq_of_mem hj
    simp [swapPairingPartners,hne]



theorem PairingOn.orderedPair_endpoints_mem {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hp : orderedEndpointPair i j ∈ P) : i ∈ S ∧ j ∈ S := by
  have h := hP.endpoints_mem hp
  unfold orderedEndpointPair at h
  split_ifs at h <;> aesop

theorem PairingOn.orderedPair_notMem {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∉ S) : orderedEndpointPair i j ∉ P :=
  fun hp => hi (hP.orderedPair_endpoints_mem hp).1

/-- Switching both partners twice restores the original occurrence set. -/
theorem PairingOn.swap_partners_involutive {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    swapPairingPartners (swapPairingPartners P i j) i j = P := by
  by_cases hne : pairingPartner P i = j
  · simp [swapPairingPartners,hne]
  · let a := pairingPartner P i
    let b := pairingPartner P j
    let Q := (P.erase (orderedEndpointPair i a)).erase (orderedEndpointPair j b)
    have hia : i ≠ a := (hP.partner_spec hi).1
    have hjb : j ≠ b := (hP.partner_spec hj).1
    obtain ⟨hbi,hab⟩ := hP.partners_disjoint hi hj hij hne
    have hQ : PairingOn ((((S.erase i).erase a).erase j).erase b) Q :=
      (hP.partner_decomposition hi hj hij hne).1
    have hn₁ : orderedEndpointPair i b ∉ Q := hQ.orderedPair_notMem (by simp)
    have hn₂ : orderedEndpointPair j a ∉ Q := hQ.orderedPair_notMem (by simp)
    have hpq : orderedEndpointPair i b ≠ orderedEndpointPair j a :=
      orderedEndpointPair_ne hij.symm hjb
    have hvalues := hP.swap_partner_values hi hj hij hne
    have hbranch : pairingPartner (swapPairingPartners P i j) i ≠ j := by
      rw [hvalues.1]
      exact hjb.symm
    rw [swapPairingPartners,if_neg hbranch,hvalues.1,hvalues.2]
    have herase : ((swapPairingPartners P i j).erase (orderedEndpointPair i b)).erase
        (orderedEndpointPair j a) = Q := by
      simp only [swapPairingPartners,if_neg hne]
      change ((insert (orderedEndpointPair i b) (insert (orderedEndpointPair j a) Q)).erase
        (orderedEndpointPair i b)).erase (orderedEndpointPair j a) = Q
      simp [hn₁,hn₂,hpq]
    change insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b)
      (((swapPairingPartners P i j).erase (orderedEndpointPair i b)).erase
        (orderedEndpointPair j a))) = P
    rw [herase]
    exact (hP.partner_decomposition hi hj hij hne).2

/-- A nontrivial partner switch cannot fix its pairing. -/
theorem PairingOn.swap_partners_ne {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hne : pairingPartner P i ≠ j) : swapPairingPartners P i j ≠ P := by
  intro heq
  have hv := (hP.swap_partner_values hi hj hij hne).1
  rw [heq] at hv
  exact (hP.partners_disjoint hi hj hij hne).2 hv



section Ring
variable {R : Type*} [CommRing R]

/-- Normalize a skew entry with its literal endpoint-order unit. -/
theorem matrix_entry_orderedEndpointPair (A : Matrix V V R)
    (hskew : ∀ u v, A v u = -A u v) (i j : V) :
    A (orderedEndpointPair i j).1 (orderedEndpointPair i j).2 =
      (endpointOrderSign i j : R) * A i j := by
  unfold orderedEndpointPair endpointOrderSign
  split_ifs <;> simp only [Int.cast_one,Int.cast_neg,one_mul,neg_mul]
  exact hskew i j

/-- Equal rows cancel the two weighted terms related by a nontrivial partner switch. -/
theorem PairingOn.signedTerm_swap {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hne : pairingPartner P i ≠ j) (A : Matrix V V R)
    (hskew : ∀ u v, A v u = -A u v) (hrows : ∀ v, A i v = A j v) :
    (pairingSign P : R) * (∏ p ∈ P, A p.1 p.2) =
      -((pairingSign (swapPairingPartners P i j) : R) *
        ∏ p ∈ swapPairingPartners P i j, A p.1 p.2) := by
  let a := pairingPartner P i
  let b := pairingPartner P j
  let Q := (P.erase (orderedEndpointPair i a)).erase (orderedEndpointPair j b)
  have hia : i ≠ a := (hP.partner_spec hi).1
  have hjb : j ≠ b := (hP.partner_spec hj).1
  obtain ⟨hbi,hab⟩ := hP.partners_disjoint hi hj hij hne
  have hQ : PairingOn ((((S.erase i).erase a).erase j).erase b) Q :=
    (hP.partner_decomposition hi hj hij hne).1
  have hrec : insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b) Q) = P :=
    (hP.partner_decomposition hi hj hij hne).2
  have hrec' : swapPairingPartners P i j =
      insert (orderedEndpointPair i b) (insert (orderedEndpointPair j a) Q) := by
    simp only [swapPairingPartners,if_neg hne]
    rfl
  have hn₁ : orderedEndpointPair i a ∉ Q := hQ.orderedPair_notMem (by simp)
  have hn₂ : orderedEndpointPair j b ∉ Q := hQ.orderedPair_notMem (by simp)
  have hn₃ : orderedEndpointPair i b ∉ Q := hQ.orderedPair_notMem (by simp)
  have hn₄ : orderedEndpointPair j a ∉ Q := hQ.orderedPair_notMem (by simp)
  have hneq : orderedEndpointPair i a ≠ orderedEndpointPair j b :=
    orderedEndpointPair_ne hij.symm hne.symm
  have hneq' : orderedEndpointPair i b ≠ orderedEndpointPair j a :=
    orderedEndpointPair_ne hij.symm hjb
  have havoid : ∀ q ∈ Q,
      (q.1 ≠ i ∧ q.1 ≠ j ∧ q.1 ≠ a ∧ q.1 ≠ b) ∧
      (q.2 ≠ i ∧ q.2 ≠ j ∧ q.2 ≠ a ∧ q.2 ≠ b) := by
    intro q hq
    have hm := hQ.endpoints_mem hq
    simp only [Finset.mem_erase] at hm
    exact ⟨⟨hm.1.2.2.2.1,hm.1.2.1,hm.1.2.2.1,hm.1.1⟩,
      ⟨hm.2.2.2.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.1⟩⟩
  have hsgn := pairingSign_exchange_partners Q i j a b hij hia hbi.symm hne.symm hjb hab hQ.2 havoid
  have hsgnR :
      (pairingSign (insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b) Q)) : R) *
          (endpointOrderSign i a : R) * (endpointOrderSign j b : R) =
        - ((pairingSign (insert (orderedEndpointPair i b) (insert (orderedEndpointPair j a) Q)) : R) *
          (endpointOrderSign i b : R) * (endpointOrderSign j a : R)) := by
    simpa only [Int.cast_mul,Int.cast_neg] using congrArg (Int.cast : ℤ → R) hsgn
  have hprod : ∀ x y z w,
      orderedEndpointPair x y ∉ Q → orderedEndpointPair z w ∉ Q →
      orderedEndpointPair x y ≠ orderedEndpointPair z w →
      (∏ p ∈ insert (orderedEndpointPair x y) (insert (orderedEndpointPair z w) Q), A p.1 p.2) =
        (endpointOrderSign x y : R) * A x y *
          ((endpointOrderSign z w : R) * A z w) * ∏ p ∈ Q, A p.1 p.2 := by
    intro x y z w hn₁ hn₂ hne
    rw [Finset.prod_insert (by simp [hn₁,hne]),Finset.prod_insert hn₂]
    rw [matrix_entry_orderedEndpointPair A hskew,matrix_entry_orderedEndpointPair A hskew]
    ring
  calc
    _ = ((pairingSign (insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b) Q)) : R) *
        (endpointOrderSign i a : R) * (endpointOrderSign j b : R)) *
          (A i a * A j b) * ∏ p ∈ Q, A p.1 p.2 := by
      conv_lhs => rw [← hrec, hprod i a j b hn₁ hn₂ hneq]
      ring
    _ = -(((pairingSign (insert (orderedEndpointPair i b) (insert (orderedEndpointPair j a) Q)) : R) *
        (endpointOrderSign i b : R) * (endpointOrderSign j a : R)) *
          (A i b * A j a) * ∏ p ∈ Q, A p.1 p.2) := by
      rw [hsgnR,hrows a,hrows b]
      ring
    _ = _ := by
      rw [hrec', hprod i b j a hn₃ hn₄ hneq']
      ring

/-- When the equal-row vertices are paired together, that matching term vanishes. -/
theorem PairingOn.signedTerm_zero_of_partner_eq {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i j : V} (hi : i ∈ S) (heq : pairingPartner P i = j)
    (A : Matrix V V R) (hskew : ∀ u v, A v u = -A u v)
    (hdiag : ∀ u, A u u = 0) (hrows : ∀ v, A i v = A j v) :
    (pairingSign P : R) * (∏ p ∈ P, A p.1 p.2) = 0 := by
  have hp := (hP.partner_spec hi).2
  rw [heq] at hp
  have hentry : A (orderedEndpointPair i j).1 (orderedEndpointPair i j).2 = 0 := by
    rw [matrix_entry_orderedEndpointPair A hskew, hrows j, hdiag j, mul_zero]
  rw [Finset.prod_eq_zero hp hentry,mul_zero]

/-- Repeated active rows in an alternating matrix make the literal supported
Pfaffian zero, including in characteristic two. Cancellation uses a fixed-point-
free involution; it does not divide by two. -/
theorem supportedPfaffian_eq_zero_of_equal_rows [Fintype V]
    (S : Finset V) (A : Matrix V V R) (i j : V) (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0)
    (hrows : ∀ v, A i v = A j v) : supportedPfaffian S A = 0 := by
  unfold supportedPfaffian
  let g : {P : Finset (V × V) // PairingOn S P} →
      {P : Finset (V × V) // PairingOn S P} := fun P =>
    ⟨swapPairingPartners P.val i j,P.property.swap_partners hi hj hij⟩
  apply Finset.sum_involution (fun P _ => g P)
  · intro P _
    by_cases h : pairingPartner P.val i = j
    · have hz := P.property.signedTerm_zero_of_partner_eq hi h A hskew hdiag hrows
      have hg : g P = P := by
        apply Subtype.ext
        simp [g,swapPairingPartners,h]
      rw [hg,hz,zero_add]
    · have he := P.property.signedTerm_swap hi hj hij h A hskew hrows
      change _ + ((pairingSign (swapPairingPartners P.val i j) : R) * _) = 0
      rw [he,neg_add_cancel]
  · intro P _ hn heq
    by_cases h : pairingPartner P.val i = j
    · exact hn (P.property.signedTerm_zero_of_partner_eq hi h A hskew hdiag hrows)
    · exact P.property.swap_partners_ne hi hj hij h (congrArg Subtype.val heq)
  · intro P _
    exact Finset.mem_univ _
  · intro P _
    apply Subtype.ext
    exact P.property.swap_partners_involutive hi hj hij

/-- Simultaneously adding `c` times a source row and column to a distinct target
preserves the literal signed pairing Pfaffian. -/
theorem supportedPfaffian_elementaryShear [Fintype V]
    (S : Finset V) (A : Matrix V V R) (source target : V) (c : R)
    (hs : source ∈ S) (ht : target ∈ S) (hne : source ≠ target)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    supportedPfaffian S (fun u v => A u v +
      (if u = target then c * A source v else 0) +
      (if v = target then c * A u source else 0)) = supportedPfaffian S A := by
  let f : V → V := fun v => if v = target then source else v
  let B : Matrix V V R := fun u v => A (f u) (f v)
  have hBskew : ∀ u v, B v u = -B u v := fun u v => hskew (f u) (f v)
  have hBdiag : ∀ u, B u u = 0 := fun u => hdiag (f u)
  have hBrows : ∀ v, B target v = B source v := by simp [B,f,hne]
  have hBzero := supportedPfaffian_eq_zero_of_equal_rows S B target source ht hs hne.symm
    hBskew hBdiag hBrows
  have heq : supportedPfaffian S (fun u v => A u v +
      (if u = target then c * A source v else 0) +
      (if v = target then c * A u source else 0)) =
      supportedPfaffian S (vertexCombination target 1 c A B) := by
    apply supportedPfaffian_congr
    intro u _ v _ huv
    have hneuv := huv.ne
    by_cases hu : u = target
    · subst u
      have hv : v ≠ target := hneuv.symm
      simp [vertexCombination,B,f,hv]
    · by_cases hv : v = target
      · subst v
        simp [vertexCombination,B,f,hu]
      · simp [vertexCombination,hu,hv]
  rw [heq,supportedPfaffian_vertexCombination S ht 1 c A B,hBzero,mul_zero,add_zero,one_mul]
  intro u _ v _ hu hv
  simp [B,f,hu,hv]

end Ring
end PlanarHom.MultiGraph
