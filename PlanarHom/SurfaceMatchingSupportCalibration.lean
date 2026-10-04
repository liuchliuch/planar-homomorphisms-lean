import PlanarHom.OccurrenceSkewCodeSemantics

/-! NEW calibration of an actual matching sign by a Pfaffian with literal
0/1 occurrence support. No Pfaffian-orientation assumption is needed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V E K : Type*} [Fintype V] [Fintype E] [LinearOrder V] [CommRing K]
variable (G : MultiGraph V E)

theorem PerfectMatching.eq_of_subset {M N : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (hsub : M⊆N) : M=N := by
  have hm := PerfectMatching.card_vertices G M hM
  have hn := PerfectMatching.card_vertices G N hN
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem pairingPfaffian_matching_support (orientation : E→Bool) (M : Finset E)
    (hM : G.PerfectMatching M) :
    pairingPfaffian (G.occurrenceSkewMatrix orientation (fun e => if e∈M then (1:K) else 0))=
      G.matchingPfaffianSign orientation M := by
  rw [G.pairingPfaffian_occurrenceSkewMatrix]
  rw [Finset.sum_eq_single (⟨M,hM⟩ : {S : Finset E // G.PerfectMatching S})]
  · have hp : (∏e∈M,if e∈M then (1:K) else 0)=1 := by
      apply Finset.prod_eq_one
      intro e he
      simp [he]
    rw [hp,mul_one]
  · intro N hN hne
    have hnot : ¬N.val⊆M := fun h => hne (Subtype.ext (N.property.eq_of_subset G hM h))
    obtain ⟨e,he,hem⟩ := Finset.not_subset.mp hnot
    have hz : (∏e∈N.val,if e∈M then (1:K) else 0)=0 :=
      Finset.prod_eq_zero he (by simp [hem])
    rw [hz,mul_zero]
  · simp

end PlanarHom.MultiGraph
