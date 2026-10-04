import PlanarHom.OccurrencePfaffianExpansion

/-! NEW reconstruction: vertexwise linearity of the literal pairing expression.
No elimination or congruence identity is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V R : Type*} [LinearOrder V] [CommRing R]

/-- Every active vertex belongs to a literal selected pair. -/
theorem PairingOn.exists_incident_pair {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) :
    ∃ p ∈ P, p.1 = i ∨ p.2 = i := by
  have hs : 0 < ∑ p ∈ P, (pairGraph V).endpointCount p i := by
    change 0 < (pairGraph V).selectedDegree P i
    rw [hP.1, if_pos hi]
    exact Nat.zero_lt_one
  obtain ⟨p,hp,hpos⟩ := Finset.sum_pos_iff.mp hs
  refine ⟨p,hp,?_⟩
  by_contra hn
  push_neg at hn
  simp [endpointCount,pairGraph,hn.1,hn.2] at hpos

/-- Distinct selected pairs are endpoint-disjoint. -/
theorem PairingOn.other_pair_avoids {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {p q : V × V} (hp : p ∈ P) (hq : q ∈ P.erase p)
    {i : V} (hip : p.1 = i ∨ p.2 = i) : q.1 ≠ i ∧ q.2 ≠ i := by
  have hmem := (hP.erase_pair hp).endpoints_mem hq
  simp only [Finset.mem_erase] at hmem
  rcases hip with rfl | rfl
  · exact ⟨hmem.1.2.1,hmem.2.2.1⟩
  · exact ⟨hmem.1.1,hmem.2.1⟩

/-- Only upper entries whose endpoints are active enter the expression. -/
theorem supportedPfaffian_congr [Fintype V] (S : Finset V) (A B : Matrix V V R)
    (h : ∀ u ∈ S, ∀ v ∈ S, u < v → A u v = B u v) :
    supportedPfaffian S A = supportedPfaffian S B := by
  unfold supportedPfaffian
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hm := P.property.endpoints_mem hp
  exact h p.1 hm.1 p.2 hm.2 (P.property.2 p hp)

/-- Linear combination in all entries incident to one vertex, with the other
entries held fixed. This definition makes no skew-symmetry assumption. -/
def vertexCombination (i : V) (a b : R) (A B : Matrix V V R) : Matrix V V R :=
  fun u v => if u = i ∨ v = i then a * A u v + b * B u v else A u v

/-- The pairing product is linear in the unique pair incident to `i`. -/
theorem PairingOn.prod_vertexCombination {S : Finset V} {P : Finset (V × V)}
    (hP : PairingOn S P) {i : V} (hi : i ∈ S) (a b : R) (A B : Matrix V V R)
    (hAB : ∀ u ∈ S, ∀ v ∈ S, u ≠ i → v ≠ i → A u v = B u v) :
    (∏ p ∈ P, vertexCombination i a b A B p.1 p.2) =
      a * (∏ p ∈ P, A p.1 p.2) + b * (∏ p ∈ P, B p.1 p.2) := by
  obtain ⟨p,hp,hip⟩ := hP.exists_incident_pair hi
  have hrestA : (∏ q ∈ P.erase p, vertexCombination i a b A B q.1 q.2) =
      ∏ q ∈ P.erase p, A q.1 q.2 := by
    apply Finset.prod_congr rfl
    intro q hq
    have ha := hP.other_pair_avoids hp hq hip
    simp [vertexCombination,ha.1,ha.2]
  have hrestB : (∏ q ∈ P.erase p, B q.1 q.2) = ∏ q ∈ P.erase p, A q.1 q.2 := by
    apply Finset.prod_congr rfl
    intro q hq
    have ha := hP.other_pair_avoids hp hq hip
    have hm := hP.endpoints_mem (Finset.mem_of_mem_erase hq)
    exact (hAB q.1 hm.1 q.2 hm.2 ha.1 ha.2).symm
  rw [← Finset.prod_erase_mul _ _ hp, ← Finset.prod_erase_mul _ _ hp,
    ← Finset.prod_erase_mul _ _ hp, hrestA, hrestB]
  simp only [vertexCombination, if_pos hip]
  ring

/-- Vertexwise multilinearity of the exact signed supported pairing Pfaffian. -/
theorem supportedPfaffian_vertexCombination [Fintype V] (S : Finset V) {i : V}
    (hi : i ∈ S) (a b : R) (A B : Matrix V V R)
    (hAB : ∀ u ∈ S, ∀ v ∈ S, u ≠ i → v ≠ i → A u v = B u v) :
    supportedPfaffian S (vertexCombination i a b A B) =
      a * supportedPfaffian S A + b * supportedPfaffian S B := by
  unfold supportedPfaffian
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [P.property.prod_vertexCombination hi a b A B hAB]
  ring

end PlanarHom.MultiGraph
