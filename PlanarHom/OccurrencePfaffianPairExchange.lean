import PlanarHom.OccurrencePfaffianVertexLinearity
import Mathlib.Tactic.Order
import Mathlib.Tactic.Linarith

/-! NEW reconstruction: exact crossing-sign relations for two replaced pairs. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

/-- The sign contributed by one endpoint strictly inside a pair. -/
def endpointIntervalSign (a b x : V) : ℤ := if a < x ∧ x < b then -1 else 1

def pairIntervalFactor (Q : Finset (V × V)) (a b : V) : ℤ :=
  ∏ q ∈ Q, endpointIntervalSign a b q.1 * endpointIntervalSign a b q.2

/-- The original crossing sign insertion law, factored per endpoint. -/
theorem pairingSign_insert_eq_intervalFactor (Q : Finset (V × V)) (a b : V)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (ha : ∀ q ∈ Q, q.1 ≠ a) (hb : ∀ q ∈ Q, q.2 ≠ b) :
    pairingSign (insert (a,b) Q) = pairIntervalFactor Q a b * pairingSign Q := by
  rw [pairingSign_insert_of_incidence Q a b hordered ha hb _ rfl]
  congr 1
  unfold pairIntervalFactor
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro q _
  by_cases h₁ : a < q.1 ∧ q.1 < b <;>
    by_cases h₂ : a < q.2 ∧ q.2 < b <;> simp [endpointIntervalSign,h₁,h₂]

/-- Rearranging four distinct endpoint intervals preserves external parity. -/
theorem endpointIntervalSign_four {a b c d x : V}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) :
    endpointIntervalSign a b x * endpointIntervalSign c d x =
      endpointIntervalSign a c x * endpointIntervalSign b d x ∧
    endpointIntervalSign a b x * endpointIntervalSign c d x =
      endpointIntervalSign a d x * endpointIntervalSign b c x := by
  by_cases ha : x < a
  · have hb := ha.trans hab
    have hc := hb.trans hbc
    have hd := hc.trans hcd
    simp [endpointIntervalSign,ha,hb,hc,hd,not_lt_of_gt ha,not_lt_of_gt hb,not_lt_of_gt hc]
  · have ha : a < x := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hx.1)
    by_cases hb : x < b
    · have hc := hb.trans hbc
      have hd := hc.trans hcd
      simp [endpointIntervalSign,ha,hb,hc,hd,not_lt_of_gt hb,not_lt_of_gt hc]
    · have hb : b < x := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hx.2.1)
      by_cases hc : x < c
      · have hd := hc.trans hcd
        simp [endpointIntervalSign,ha,hb,hc,hd,not_lt_of_gt hb,not_lt_of_gt hc]
      · have hc : c < x := lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm hx.2.2.1)
        by_cases hd : x < d
        · simp [endpointIntervalSign,ha,hb,hc,hd,not_lt_of_gt hb,not_lt_of_gt hc]
        · have hd : d < x := lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm hx.2.2.2)
          simp [endpointIntervalSign,ha,hb,hc,hd,not_lt_of_gt hb,not_lt_of_gt hc,not_lt_of_gt hd]

/-- The product over all old endpoints is the same in each four-endpoint pairing. -/
theorem pairIntervalFactor_four (Q : Finset (V × V)) {a b c d : V}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (havoid : ∀ q ∈ Q,
      (q.1 ≠ a ∧ q.1 ≠ b ∧ q.1 ≠ c ∧ q.1 ≠ d) ∧
      (q.2 ≠ a ∧ q.2 ≠ b ∧ q.2 ≠ c ∧ q.2 ≠ d)) :
    pairIntervalFactor Q a b * pairIntervalFactor Q c d =
      pairIntervalFactor Q a c * pairIntervalFactor Q b d ∧
    pairIntervalFactor Q a b * pairIntervalFactor Q c d =
      pairIntervalFactor Q a d * pairIntervalFactor Q b c := by
  unfold pairIntervalFactor
  simp only [← Finset.prod_mul_distrib]
  constructor
  · apply Finset.prod_congr rfl
    intro q hq
    have h₁ := (endpointIntervalSign_four hab hbc hcd (havoid q hq).1).1
    have h₂ := (endpointIntervalSign_four hab hbc hcd (havoid q hq).2).1
    calc
      _ = (endpointIntervalSign a b q.1 * endpointIntervalSign c d q.1) *
          (endpointIntervalSign a b q.2 * endpointIntervalSign c d q.2) := by ring
      _ = _ := by rw [h₁,h₂]; ring
  · apply Finset.prod_congr rfl
    intro q hq
    have h₁ := (endpointIntervalSign_four hab hbc hcd (havoid q hq).1).2
    have h₂ := (endpointIntervalSign_four hab hbc hcd (havoid q hq).2).2
    calc
      _ = (endpointIntervalSign a b q.1 * endpointIntervalSign c d q.1) *
          (endpointIntervalSign a b q.2 * endpointIntervalSign c d q.2) := by ring
      _ = _ := by rw [h₁,h₂]; ring

/-- The three two-pair signs have the literal `+,-,+` relation, regardless of
all remaining pairs. Only endpoint disjointness and ordering are used. -/
theorem pairingSign_four_pairings (Q : Finset (V × V)) {a b c d : V}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q,
      (q.1 ≠ a ∧ q.1 ≠ b ∧ q.1 ≠ c ∧ q.1 ≠ d) ∧
      (q.2 ≠ a ∧ q.2 ≠ b ∧ q.2 ≠ c ∧ q.2 ≠ d)) :
    pairingSign (insert (a,b) (insert (c,d) Q)) =
      -pairingSign (insert (a,c) (insert (b,d) Q)) ∧
    pairingSign (insert (a,b) (insert (c,d) Q)) =
      pairingSign (insert (a,d) (insert (b,c) Q)) := by
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  have hnot (x y : V) (hx : x = a ∨ x = b ∨ x = c ∨ x = d) : (x,y) ∉ Q := by
    intro h
    have hv := (havoid (x,y) h).1
    rcases hx with rfl | rfl | rfl | rfl
    · exact hv.1 rfl
    · exact hv.2.1 rfl
    · exact hv.2.2.1 rfl
    · exact hv.2.2.2 rfl
  have hfac := pairIntervalFactor_four Q hab hbc hcd havoid
  have habcd : pairingSign (insert (a,b) (insert (c,d) Q)) =
      pairIntervalFactor Q a b * pairIntervalFactor Q c d * pairingSign Q := by
    rw [pairingSign_insert_eq_intervalFactor _ a b
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hcd; exact hordered q hq)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hac.ne'; exact (havoid q hq).1.1)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hbd.ne'; exact (havoid q hq).2.2.1)]
    rw [pairingSign_insert_eq_intervalFactor Q c d hordered
      (fun q hq => (havoid q hq).1.2.2.1) (fun q hq => (havoid q hq).2.2.2.2)]
    rw [pairIntervalFactor,Finset.prod_insert (hnot c d (Or.inr (Or.inr (Or.inl rfl))))]
    simp [endpointIntervalSign,not_lt_of_gt hbc,not_lt_of_gt hbd,pairIntervalFactor,mul_assoc]
  have hacbd : pairingSign (insert (a,c) (insert (b,d) Q)) =
      -(pairIntervalFactor Q a c * pairIntervalFactor Q b d * pairingSign Q) := by
    rw [pairingSign_insert_eq_intervalFactor _ a c
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hbd; exact hordered q hq)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hab.ne'; exact (havoid q hq).1.1)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hcd.ne'; exact (havoid q hq).2.2.2.1)]
    rw [pairingSign_insert_eq_intervalFactor Q b d hordered
      (fun q hq => (havoid q hq).1.2.1) (fun q hq => (havoid q hq).2.2.2.2)]
    rw [pairIntervalFactor,Finset.prod_insert (hnot b d (Or.inr (Or.inl rfl)))]
    simp [endpointIntervalSign,hab,hbc,not_lt_of_gt hcd,pairIntervalFactor,mul_assoc]
  have hadbc : pairingSign (insert (a,d) (insert (b,c) Q)) =
      pairIntervalFactor Q a d * pairIntervalFactor Q b c * pairingSign Q := by
    rw [pairingSign_insert_eq_intervalFactor _ a d
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hbc; exact hordered q hq)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hab.ne'; exact (havoid q hq).1.1)
      (by intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hcd.ne; exact (havoid q hq).2.2.2.2)]
    rw [pairingSign_insert_eq_intervalFactor Q b c hordered
      (fun q hq => (havoid q hq).1.2.1) (fun q hq => (havoid q hq).2.2.2.1)]
    rw [pairIntervalFactor,Finset.prod_insert (hnot b c (Or.inr (Or.inl rfl)))]
    simp [endpointIntervalSign,hab,hac,hbd,hcd,pairIntervalFactor,mul_assoc]
  rw [habcd,hacbd,hadbc,neg_neg]
  exact ⟨congrArg (fun x => x * pairingSign Q) hfac.1,
    congrArg (fun x => x * pairingSign Q) hfac.2⟩



/-- Normalized endpoint pair for distinct endpoints. -/
def orderedEndpointPair (a b : V) : V × V := if a < b then (a,b) else (b,a)

def endpointOrderSign (a b : V) : ℤ := if a < b then 1 else -1


set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- Swapping the partners of two disjoint pairs reverses the oriented sign. -/
theorem pairingSign_exchange_partners (Q : Finset (V × V)) (i j a b : V)
    (hij : i ≠ j) (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b)
    (hordered : ∀ q ∈ Q, q.1 < q.2)
    (havoid : ∀ q ∈ Q,
      (q.1 ≠ i ∧ q.1 ≠ j ∧ q.1 ≠ a ∧ q.1 ≠ b) ∧
      (q.2 ≠ i ∧ q.2 ≠ j ∧ q.2 ≠ a ∧ q.2 ≠ b)) :
    pairingSign (insert (orderedEndpointPair i a) (insert (orderedEndpointPair j b) Q)) *
        endpointOrderSign i a * endpointOrderSign j b =
      - (pairingSign (insert (orderedEndpointPair i b) (insert (orderedEndpointPair j a) Q)) *
        endpointOrderSign i b * endpointOrderSign j a) := by
  rcases lt_or_gt_of_ne (hij.symm) with h_ji | h_ij
  · rcases lt_or_gt_of_ne (hja.symm) with h_aj | h_ja
    · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
      · have h_bj : b < j := h_ba.trans h_aj
        have h_bi : b < i := h_bj.trans h_ji
        have h_ai : a < i := h_aj.trans h_ji
        have hh4 := pairingSign_four_pairings Q h_ba h_aj h_ji hordered (by
          intro q hq
          have hh := havoid q hq
          exact ⟨⟨hh.1.2.2.2, hh.1.2.2.1, hh.1.2.1, hh.1.1⟩, ⟨hh.2.2.2.2, hh.2.2.2.1, hh.2.2.1, hh.2.1⟩⟩)
        simp only [orderedEndpointPair, endpointOrderSign,
          h_ba,h_bj,h_bi,h_aj,h_ai,h_ji,
          not_lt_of_gt h_ba,not_lt_of_gt h_bj,not_lt_of_gt h_bi,not_lt_of_gt h_aj,not_lt_of_gt h_ai,not_lt_of_gt h_ji,
          if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
        linarith [hh4.1, hh4.2]
      · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
        · have h_ai : a < i := h_aj.trans h_ji
          have h_bi : b < i := h_bj.trans h_ji
          have hh4 := pairingSign_four_pairings Q h_ab h_bj h_ji hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.1, hh.1.2.2.2, hh.1.2.1, hh.1.1⟩, ⟨hh.2.2.2.1, hh.2.2.2.2, hh.2.2.1, hh.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_ab,h_aj,h_ai,h_bj,h_bi,h_ji,
            not_lt_of_gt h_ab,not_lt_of_gt h_aj,not_lt_of_gt h_ai,not_lt_of_gt h_bj,not_lt_of_gt h_bi,not_lt_of_gt h_ji,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
          · have h_ai : a < i := h_ab.trans h_bi
            have hh4 := pairingSign_four_pairings Q h_aj h_jb h_bi hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.2.1, hh.1.2.1, hh.1.2.2.2, hh.1.1⟩, ⟨hh.2.2.2.1, hh.2.2.1, hh.2.2.2.2, hh.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_aj,h_ab,h_ai,h_jb,h_ji,h_bi,
              not_lt_of_gt h_aj,not_lt_of_gt h_ab,not_lt_of_gt h_ai,not_lt_of_gt h_jb,not_lt_of_gt h_ji,not_lt_of_gt h_bi,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · have h_ai : a < i := h_aj.trans h_ji
            have hh4 := pairingSign_four_pairings Q h_aj h_ji h_ib hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.2.1, hh.1.2.1, hh.1.1, hh.1.2.2.2⟩, ⟨hh.2.2.2.1, hh.2.2.1, hh.2.1, hh.2.2.2.2⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_aj,h_ai,h_ab,h_ji,h_jb,h_ib,
              not_lt_of_gt h_aj,not_lt_of_gt h_ai,not_lt_of_gt h_ab,not_lt_of_gt h_ji,not_lt_of_gt h_jb,not_lt_of_gt h_ib,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
    · rcases lt_or_gt_of_ne (hia.symm) with h_ai | h_ia
      · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
        · have h_ba : b < a := h_bj.trans h_ja
          have h_bi : b < i := h_ba.trans h_ai
          have hh4 := pairingSign_four_pairings Q h_bj h_ja h_ai hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.2, hh.1.2.1, hh.1.2.2.1, hh.1.1⟩, ⟨hh.2.2.2.2, hh.2.2.1, hh.2.2.2.1, hh.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_bj,h_ba,h_bi,h_ja,h_ji,h_ai,
            not_lt_of_gt h_bj,not_lt_of_gt h_ba,not_lt_of_gt h_bi,not_lt_of_gt h_ja,not_lt_of_gt h_ji,not_lt_of_gt h_ai,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
          · have h_bi : b < i := h_ba.trans h_ai
            have hh4 := pairingSign_four_pairings Q h_jb h_ba h_ai hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.1, hh.1.2.2.2, hh.1.2.2.1, hh.1.1⟩, ⟨hh.2.2.1, hh.2.2.2.2, hh.2.2.2.1, hh.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_jb,h_ja,h_ji,h_ba,h_bi,h_ai,
              not_lt_of_gt h_jb,not_lt_of_gt h_ja,not_lt_of_gt h_ji,not_lt_of_gt h_ba,not_lt_of_gt h_bi,not_lt_of_gt h_ai,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
            · have hh4 := pairingSign_four_pairings Q h_ja h_ab h_bi hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.2.1, hh.1.2.2.1, hh.1.2.2.2, hh.1.1⟩, ⟨hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2, hh.2.1⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ja,h_jb,h_ji,h_ab,h_ai,h_bi,
                not_lt_of_gt h_ja,not_lt_of_gt h_jb,not_lt_of_gt h_ji,not_lt_of_gt h_ab,not_lt_of_gt h_ai,not_lt_of_gt h_bi,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
            · have hh4 := pairingSign_four_pairings Q h_ja h_ai h_ib hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.2.1, hh.1.2.2.1, hh.1.1, hh.1.2.2.2⟩, ⟨hh.2.2.1, hh.2.2.2.1, hh.2.1, hh.2.2.2.2⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ja,h_ji,h_jb,h_ai,h_ab,h_ib,
                not_lt_of_gt h_ja,not_lt_of_gt h_ji,not_lt_of_gt h_jb,not_lt_of_gt h_ai,not_lt_of_gt h_ab,not_lt_of_gt h_ib,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
      · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
        · have h_bi : b < i := h_bj.trans h_ji
          have h_ba : b < a := h_bi.trans h_ia
          have hh4 := pairingSign_four_pairings Q h_bj h_ji h_ia hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.2, hh.1.2.1, hh.1.1, hh.1.2.2.1⟩, ⟨hh.2.2.2.2, hh.2.2.1, hh.2.1, hh.2.2.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_bj,h_bi,h_ba,h_ji,h_ja,h_ia,
            not_lt_of_gt h_bj,not_lt_of_gt h_bi,not_lt_of_gt h_ba,not_lt_of_gt h_ji,not_lt_of_gt h_ja,not_lt_of_gt h_ia,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
          · have h_ba : b < a := h_bi.trans h_ia
            have hh4 := pairingSign_four_pairings Q h_jb h_bi h_ia hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.1, hh.1.2.2.2, hh.1.1, hh.1.2.2.1⟩, ⟨hh.2.2.1, hh.2.2.2.2, hh.2.1, hh.2.2.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_jb,h_ji,h_ja,h_bi,h_ba,h_ia,
              not_lt_of_gt h_jb,not_lt_of_gt h_ji,not_lt_of_gt h_ja,not_lt_of_gt h_bi,not_lt_of_gt h_ba,not_lt_of_gt h_ia,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
            · have hh4 := pairingSign_four_pairings Q h_ji h_ib h_ba hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.2.1, hh.1.1, hh.1.2.2.2, hh.1.2.2.1⟩, ⟨hh.2.2.1, hh.2.1, hh.2.2.2.2, hh.2.2.2.1⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ji,h_jb,h_ja,h_ib,h_ia,h_ba,
                not_lt_of_gt h_ji,not_lt_of_gt h_jb,not_lt_of_gt h_ja,not_lt_of_gt h_ib,not_lt_of_gt h_ia,not_lt_of_gt h_ba,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
            · have hh4 := pairingSign_four_pairings Q h_ji h_ia h_ab hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.2.1, hh.1.1, hh.1.2.2.1, hh.1.2.2.2⟩, ⟨hh.2.2.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ji,h_ja,h_jb,h_ia,h_ib,h_ab,
                not_lt_of_gt h_ji,not_lt_of_gt h_ja,not_lt_of_gt h_jb,not_lt_of_gt h_ia,not_lt_of_gt h_ib,not_lt_of_gt h_ab,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
  · rcases lt_or_gt_of_ne (hia.symm) with h_ai | h_ia
    · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
      · have h_bi : b < i := h_ba.trans h_ai
        have h_bj : b < j := h_bi.trans h_ij
        have h_aj : a < j := h_ai.trans h_ij
        have hh4 := pairingSign_four_pairings Q h_ba h_ai h_ij hordered (by
          intro q hq
          have hh := havoid q hq
          exact ⟨⟨hh.1.2.2.2, hh.1.2.2.1, hh.1.1, hh.1.2.1⟩, ⟨hh.2.2.2.2, hh.2.2.2.1, hh.2.1, hh.2.2.1⟩⟩)
        simp only [orderedEndpointPair, endpointOrderSign,
          h_ba,h_bi,h_bj,h_ai,h_aj,h_ij,
          not_lt_of_gt h_ba,not_lt_of_gt h_bi,not_lt_of_gt h_bj,not_lt_of_gt h_ai,not_lt_of_gt h_aj,not_lt_of_gt h_ij,
          if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
        linarith [hh4.1, hh4.2]
      · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
        · have h_aj : a < j := h_ai.trans h_ij
          have h_bj : b < j := h_bi.trans h_ij
          have hh4 := pairingSign_four_pairings Q h_ab h_bi h_ij hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.1, hh.1.2.2.2, hh.1.1, hh.1.2.1⟩, ⟨hh.2.2.2.1, hh.2.2.2.2, hh.2.1, hh.2.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_ab,h_ai,h_aj,h_bi,h_bj,h_ij,
            not_lt_of_gt h_ab,not_lt_of_gt h_ai,not_lt_of_gt h_aj,not_lt_of_gt h_bi,not_lt_of_gt h_bj,not_lt_of_gt h_ij,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
          · have h_aj : a < j := h_ab.trans h_bj
            have hh4 := pairingSign_four_pairings Q h_ai h_ib h_bj hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.2.1, hh.1.1, hh.1.2.2.2, hh.1.2.1⟩, ⟨hh.2.2.2.1, hh.2.1, hh.2.2.2.2, hh.2.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_ai,h_ab,h_aj,h_ib,h_ij,h_bj,
              not_lt_of_gt h_ai,not_lt_of_gt h_ab,not_lt_of_gt h_aj,not_lt_of_gt h_ib,not_lt_of_gt h_ij,not_lt_of_gt h_bj,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · have h_aj : a < j := h_ai.trans h_ij
            have hh4 := pairingSign_four_pairings Q h_ai h_ij h_jb hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.2.2.1, hh.1.1, hh.1.2.1, hh.1.2.2.2⟩, ⟨hh.2.2.2.1, hh.2.1, hh.2.2.1, hh.2.2.2.2⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_ai,h_aj,h_ab,h_ij,h_ib,h_jb,
              not_lt_of_gt h_ai,not_lt_of_gt h_aj,not_lt_of_gt h_ab,not_lt_of_gt h_ij,not_lt_of_gt h_ib,not_lt_of_gt h_jb,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
    · rcases lt_or_gt_of_ne (hja.symm) with h_aj | h_ja
      · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
        · have h_ba : b < a := h_bi.trans h_ia
          have h_bj : b < j := h_ba.trans h_aj
          have hh4 := pairingSign_four_pairings Q h_bi h_ia h_aj hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.2, hh.1.1, hh.1.2.2.1, hh.1.2.1⟩, ⟨hh.2.2.2.2, hh.2.1, hh.2.2.2.1, hh.2.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_bi,h_ba,h_bj,h_ia,h_ij,h_aj,
            not_lt_of_gt h_bi,not_lt_of_gt h_ba,not_lt_of_gt h_bj,not_lt_of_gt h_ia,not_lt_of_gt h_ij,not_lt_of_gt h_aj,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
          · have h_bj : b < j := h_ba.trans h_aj
            have hh4 := pairingSign_four_pairings Q h_ib h_ba h_aj hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.1, hh.1.2.2.2, hh.1.2.2.1, hh.1.2.1⟩, ⟨hh.2.1, hh.2.2.2.2, hh.2.2.2.1, hh.2.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_ib,h_ia,h_ij,h_ba,h_bj,h_aj,
              not_lt_of_gt h_ib,not_lt_of_gt h_ia,not_lt_of_gt h_ij,not_lt_of_gt h_ba,not_lt_of_gt h_bj,not_lt_of_gt h_aj,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
            · have hh4 := pairingSign_four_pairings Q h_ia h_ab h_bj hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.1, hh.1.2.2.1, hh.1.2.2.2, hh.1.2.1⟩, ⟨hh.2.1, hh.2.2.2.1, hh.2.2.2.2, hh.2.2.1⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ia,h_ib,h_ij,h_ab,h_aj,h_bj,
                not_lt_of_gt h_ia,not_lt_of_gt h_ib,not_lt_of_gt h_ij,not_lt_of_gt h_ab,not_lt_of_gt h_aj,not_lt_of_gt h_bj,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
            · have hh4 := pairingSign_four_pairings Q h_ia h_aj h_jb hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.1, hh.1.2.2.1, hh.1.2.1, hh.1.2.2.2⟩, ⟨hh.2.1, hh.2.2.2.1, hh.2.2.1, hh.2.2.2.2⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ia,h_ij,h_ib,h_aj,h_ab,h_jb,
                not_lt_of_gt h_ia,not_lt_of_gt h_ij,not_lt_of_gt h_ib,not_lt_of_gt h_aj,not_lt_of_gt h_ab,not_lt_of_gt h_jb,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
      · rcases lt_or_gt_of_ne (hib.symm) with h_bi | h_ib
        · have h_bj : b < j := h_bi.trans h_ij
          have h_ba : b < a := h_bj.trans h_ja
          have hh4 := pairingSign_four_pairings Q h_bi h_ij h_ja hordered (by
            intro q hq
            have hh := havoid q hq
            exact ⟨⟨hh.1.2.2.2, hh.1.1, hh.1.2.1, hh.1.2.2.1⟩, ⟨hh.2.2.2.2, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩⟩)
          simp only [orderedEndpointPair, endpointOrderSign,
            h_bi,h_bj,h_ba,h_ij,h_ia,h_ja,
            not_lt_of_gt h_bi,not_lt_of_gt h_bj,not_lt_of_gt h_ba,not_lt_of_gt h_ij,not_lt_of_gt h_ia,not_lt_of_gt h_ja,
            if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
          linarith [hh4.1, hh4.2]
        · rcases lt_or_gt_of_ne (hjb.symm) with h_bj | h_jb
          · have h_ba : b < a := h_bj.trans h_ja
            have hh4 := pairingSign_four_pairings Q h_ib h_bj h_ja hordered (by
              intro q hq
              have hh := havoid q hq
              exact ⟨⟨hh.1.1, hh.1.2.2.2, hh.1.2.1, hh.1.2.2.1⟩, ⟨hh.2.1, hh.2.2.2.2, hh.2.2.1, hh.2.2.2.1⟩⟩)
            simp only [orderedEndpointPair, endpointOrderSign,
              h_ib,h_ij,h_ia,h_bj,h_ba,h_ja,
              not_lt_of_gt h_ib,not_lt_of_gt h_ij,not_lt_of_gt h_ia,not_lt_of_gt h_bj,not_lt_of_gt h_ba,not_lt_of_gt h_ja,
              if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
            linarith [hh4.1, hh4.2]
          · rcases lt_or_gt_of_ne (hab.symm) with h_ba | h_ab
            · have hh4 := pairingSign_four_pairings Q h_ij h_jb h_ba hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.1, hh.1.2.1, hh.1.2.2.2, hh.1.2.2.1⟩, ⟨hh.2.1, hh.2.2.1, hh.2.2.2.2, hh.2.2.2.1⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ij,h_ib,h_ia,h_jb,h_ja,h_ba,
                not_lt_of_gt h_ij,not_lt_of_gt h_ib,not_lt_of_gt h_ia,not_lt_of_gt h_jb,not_lt_of_gt h_ja,not_lt_of_gt h_ba,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]
            · have hh4 := pairingSign_four_pairings Q h_ij h_ja h_ab hordered (by
                intro q hq
                have hh := havoid q hq
                exact ⟨⟨hh.1.1, hh.1.2.1, hh.1.2.2.1, hh.1.2.2.2⟩, ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩⟩)
              simp only [orderedEndpointPair, endpointOrderSign,
                h_ij,h_ia,h_ib,h_ja,h_jb,h_ab,
                not_lt_of_gt h_ij,not_lt_of_gt h_ia,not_lt_of_gt h_ib,not_lt_of_gt h_ja,not_lt_of_gt h_jb,not_lt_of_gt h_ab,
                if_true,if_false,mul_one,mul_neg_one,neg_neg,Finset.insert_comm] at hh4 ⊢
              linarith [hh4.1, hh4.2]

end PlanarHom.MultiGraph
