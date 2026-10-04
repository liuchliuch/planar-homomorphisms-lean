import PlanarHom.OccurrencePfaffianMatrix

/-!
# Occurrence matchings and ordered pairings

The finite bijection in this file retains every parallel occurrence separately.
It is independent of any orientation, weight, drawing, or embedding algorithm.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph
variable {V E F : Type*}


/-- Endpoint incidence multiplicity of a single occurrence, including both ends
of a loop. -/
def endpointCount (G : MultiGraph V E) (e : E) (v : V) : ℕ :=
  (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0)

theorem selectedDegree_eq_sum_endpointCount (G : MultiGraph V E)
    (M : Finset E) (v : V) : G.selectedDegree M v = ∑ e ∈ M, G.endpointCount e v := rfl

/-- Distinct selected occurrences of a perfect matching cannot meet. -/
theorem PerfectMatching.eq_of_endpointCount_pos (G : MultiGraph V E)
    {M : Finset E} (hM : G.PerfectMatching M) {e f : E} (he : e ∈ M) (hf : f ∈ M)
    {v : V} (hev : 0 < G.endpointCount e v) (hfv : 0 < G.endpointCount f v) : e = f := by
  by_contra hne
  have hsub : ({e, f} : Finset E) ⊆ M := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact he
    · exact hf
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun a (_ : a ∈ M) _ => Nat.zero_le (G.endpointCount a v))
  have hsum : (∑ a ∈ M, G.endpointCount a v) = 1 := hM v
  rw [hsum] at hle
  simp [hne] at hle
  omega

/-- An endpoint-preserving map may identify parallel occurrences, but is
injective on every particular perfect matching. -/
theorem PerfectMatching.injOn_edgeMap (G : MultiGraph V E) (H : MultiGraph V F)
    (p : E → F) (hp : ∀ e v, H.endpointCount (p e) v = G.endpointCount e v)
    {M : Finset E} (hM : G.PerfectMatching M) : Set.InjOn p M := by
  intro e he f hf hef
  apply hM.eq_of_endpointCount_pos G he hf (v := G.src e)
  · simp [endpointCount]
  · rw [← hp, ← hef, hp]
    simp [endpointCount]

/-- Selected degree is preserved by an injective edge-occurrence map. -/
theorem selectedDegree_image (G : MultiGraph V E) (H : MultiGraph V F)
    (p : E → F) (hp : ∀ e v, H.endpointCount (p e) v = G.endpointCount e v)
    (M : Finset E) (hM : Set.InjOn p M) (v : V) :
    H.selectedDegree (M.image p) v = G.selectedDegree M v := by
  simp only [selectedDegree_eq_sum_endpointCount]
  rw [Finset.sum_image hM]
  exact Finset.sum_congr rfl (fun e _ => hp e v)

/-- Canonical endpoint projection preserves a perfect matching even when the
ambient graph has parallel occurrences. -/
theorem PerfectMatching.image_edgeMap (G : MultiGraph V E) (H : MultiGraph V F)
    (p : E → F) (hp : ∀ e v, H.endpointCount (p e) v = G.endpointCount e v)
    {M : Finset E} (hM : G.PerfectMatching M) : H.PerfectMatching (M.image p) := by
  intro v
  rw [selectedDegree_image G H p hp M (hM.injOn_edgeMap G H p hp), hM]

/-- Ordered-pair endpoint graph. Only strict upper-triangular pairs will be
used in a pairing; loops are consequently excluded. -/
def pairGraph (V : Type*) : MultiGraph V (V × V) := ⟨Prod.fst, Prod.snd⟩

/-- A pairing of the vertex set, normalized by putting the smaller endpoint
first in every pair. -/
def IsPairing [LinearOrder V] (P : Finset (V × V)) : Prop :=
  (pairGraph V).PerfectMatching P ∧ ∀ p ∈ P, p.1 < p.2

/-- The usual crossing-number sign of an ordered pairing. The strict
inequalities count each crossing exactly once. -/
def pairingCrossings [LinearOrder V] (P : Finset (V × V)) : ℕ :=
  ((P ×ˢ P).filter fun pq => pq.1.1 < pq.2.1 ∧ pq.2.1 < pq.1.2 ∧ pq.1.2 < pq.2.2).card

/-- Sign used in the actual signed pairing expansion of a Pfaffian. -/
def pairingSign [LinearOrder V] (P : Finset (V × V)) : ℤ :=
  (-1) ^ pairingCrossings P

theorem pairingSign_sq [LinearOrder V] (P : Finset (V × V)) : pairingSign P ^ 2 = 1 := by
  rw [pairingSign, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- The literal signed pairing expansion. This definition uses no determinant
square root and is valid over any commutative ring. -/
def pairingPfaffian [Fintype V] [LinearOrder V] {R : Type*} [CommRing R]
    (A : Matrix V V R) : R :=
  ∑ P : {P : Finset (V × V) // IsPairing P},
    (pairingSign P.val : R) * ∏ p ∈ P.val, A p.1 p.2


/-- Evaluating the pairing expression in a larger coefficient ring commutes
with the Pfaffian. In particular, the expression creates no new field constants. -/
theorem pairingPfaffian_map [Fintype V] [LinearOrder V]
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix V V R) :
    f (pairingPfaffian A) = pairingPfaffian (fun i j => f (A i j)) := by
  simp [pairingPfaffian]

/-- Odd vertex cardinality has no pairings, so its signed pairing expansion is
zero. This fact is independent of matrix entries and their possible vanishing. -/
theorem pairingPfaffian_eq_zero_of_odd [Fintype V] [LinearOrder V]
    {R : Type*} [CommRing R] (hV : Odd (Fintype.card V)) (A : Matrix V V R) :
    pairingPfaffian A = 0 := by
  have hempty : IsEmpty {P : Finset (V × V) // IsPairing P} := ⟨fun P => by
    have hcard := P.property.1.card_vertices (pairGraph V) P.val
    rw [hcard] at hV
    exact (Nat.not_even_iff_odd.mpr hV) (even_two_mul _)⟩
  simp [pairingPfaffian]

section EdgeFibers
variable (G : MultiGraph V E) (H : MultiGraph V F) (p : E → F)
variable (hp : ∀ e v, H.endpointCount (p e) v = G.endpointCount e v)

/-- One separate edge occurrence is chosen for each edge of a projected
matching. Parallel choices remain distinct elements of this finite type. -/
abbrev EdgeSections (P : Finset F) := ∀ f : P, {e : E // p e = f.val}

def sectionEdges {P : Finset F} (s : EdgeSections p P) : Finset E :=
  Finset.univ.image (fun f => (s f).val)

theorem section_injective {P : Finset F} (s : EdgeSections p P) :
    Function.Injective (fun f => (s f).val) := by
  intro a b hab
  apply Subtype.ext
  exact (s a).property.symm.trans ((congrArg p hab).trans (s b).property)

theorem sectionEdges_image {P : Finset F} (s : EdgeSections p P) :
    (sectionEdges p s).image p = P := by
  ext f
  simp only [sectionEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, ⟨a, rfl⟩, rfl⟩
    rw [(s a).property]
    exact a.property
  · intro hf
    exact ⟨(s ⟨f,hf⟩).val, ⟨⟨f,hf⟩, rfl⟩, (s ⟨f,hf⟩).property⟩

include hp in
theorem sectionEdges_perfect {P : Finset F} (hP : H.PerfectMatching P)
    (s : EdgeSections p P) : G.PerfectMatching (sectionEdges p s) := by
  intro v
  rw [selectedDegree_eq_sum_endpointCount, sectionEdges,
    Finset.sum_image (section_injective p s).injOn]
  have hterm (f : P) : G.endpointCount (s f).val v = H.endpointCount f.val v := by
    rw [← hp, (s f).property]
  simp_rw [hterm]
  change (∑ f ∈ P.attach, H.endpointCount f.val v) = 1
  exact (Finset.sum_attach P (fun f => H.endpointCount f v)).trans (hP v)

theorem prod_sectionEdges {R : Type*} [CommMonoid R] {P : Finset F}
    (s : EdgeSections p P) (w : E → R) :
    (∏ e ∈ sectionEdges p s, w e) = ∏ f : P, w (s f).val := by
  exact Finset.prod_image (section_injective p s).injOn

/-- Choose the unique occurrence over each pair in one fixed matching.
Uniqueness, rather than nonzero weights, makes this inverse valid. -/
def matchingSection (M : Finset E) : EdgeSections p (M.image p) := fun f =>
  ⟨Classical.choose (Finset.mem_image.mp f.property),
    (Classical.choose_spec (Finset.mem_image.mp f.property)).2⟩

theorem matchingSection_mem (M : Finset E) (f : M.image p) :
    (matchingSection p M f).val ∈ M :=
  (Classical.choose_spec (Finset.mem_image.mp f.property)).1

include hp in
theorem sectionEdges_matchingSection {M : Finset E} (hM : G.PerfectMatching M) :
    sectionEdges p (matchingSection p M) = M := by
  ext e
  constructor
  · intro he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact matchingSection_mem p M f
  · intro he
    let f : M.image p := ⟨p e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    apply hM.injOn_edgeMap G H p hp (matchingSection_mem p M f) he
    exact (matchingSection p M f).property

/-- The exact occurrence/section bijection. No matching existence, orientation,
positivity, or effective embedding is assumed. -/
def matchingSectionsEquiv :
    (Σ P : {P : Finset F // H.PerfectMatching P}, EdgeSections p P.val) ≃
      {M : Finset E // G.PerfectMatching M} :=
  Equiv.ofBijective
    (fun a => ⟨sectionEdges p a.2, sectionEdges_perfect G H p hp a.1.property a.2⟩)
    (by
      constructor
      · rintro ⟨⟨P, hP⟩, s⟩ ⟨⟨Q, hQ⟩, t⟩ heq
        have hst : sectionEdges p s = sectionEdges p t := congrArg Subtype.val heq
        have hPQ : P = Q := by
          exact (sectionEdges_image p s).symm.trans
            ((congrArg (fun M => M.image p) hst).trans (sectionEdges_image p t))
        subst Q
        have hchoices : s = t := by
          funext f
          apply Subtype.ext
          apply (sectionEdges_perfect G H p hp hP s).injOn_edgeMap G H p hp
          · exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
          · rw [hst]
            exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
          · exact (s f).property.trans (t f).property.symm
        subst t
        rfl
      · intro M
        refine ⟨⟨⟨M.val.image p, M.property.image_edgeMap G H p hp⟩,
          matchingSection p M.val⟩, ?_⟩
        exact Subtype.ext (sectionEdges_matchingSection G H p hp M.property))

include hp in
/-- Distributing each summed matrix coefficient chooses one genuine occurrence
per projected pair. This identity holds with arbitrary commutative-semiring
weights, including zero and (over a ring) negative weights. -/
theorem sum_matching_fiber_products [Fintype E] [Fintype F]
    {R : Type*} [CommSemiring R] (w : E → R) (c : Finset F → R) :
    (∑ P : {P : Finset F // H.PerfectMatching P}, c P.val *
      ∏ f ∈ P.val, ∑ e : {e : E // p e = f}, w e.val) =
    ∑ M : {M : Finset E // G.PerfectMatching M},
      c (M.val.image p) * ∏ e ∈ M.val, w e := by
  have hexpand (P : {P : Finset F // H.PerfectMatching P}) :
      (∏ f ∈ P.val, ∑ e : {e : E // p e = f}, w e.val) =
        ∑ s : EdgeSections p P.val, ∏ f : P.val, w (s f).val := by
    rw [← Finset.prod_coe_sort P.val (fun f => ∑ e : {e : E // p e = f}, w e.val)]
    exact Fintype.prod_sum (fun (f : P.val) (e : {e : E // p e = f.val}) => w e.val)
  simp_rw [hexpand, Finset.mul_sum]
  rw [← Fintype.sum_sigma (fun a : Σ P : {P : Finset F // H.PerfectMatching P},
    EdgeSections p P.val => c a.1.val * ∏ f : a.1.val, w (a.2 f).val)]
  apply Fintype.sum_equiv (matchingSectionsEquiv G H p hp)
  intro a
  change c a.1.val * (∏ f : a.1.val, w (a.2 f).val) =
    c ((sectionEdges p a.2).image p) * ∏ e ∈ sectionEdges p a.2, w e
  rw [sectionEdges_image, prod_sectionEdges]

end EdgeFibers

/-- Rewriting a subtype-indexed finite sum as a literal guarded sum. -/
theorem sum_subtype_eq_ite {A R : Type*} [Fintype A] [AddCommMonoid R]
    (q : A → Prop) (f : A → R) :
    (∑ a : {a : A // q a}, f a.val) = ∑ a, if q a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter q) (by simp) f]
  exact Finset.sum_filter q f

section Canonical
variable [LinearOrder V]
local instance (priority := high) : DecidableEq (V × V) := Classical.decEq (V × V)


/-- Canonicalization preserves literal incidence degree, including loops. -/
theorem canonicalPair_endpointCount (G : MultiGraph V E) (e : E) (v : V) :
    (pairGraph V).endpointCount (G.canonicalPair e) v = G.endpointCount e v := by
  classical
  unfold endpointCount pairGraph
  by_cases he : G.src e ≤ G.dst e
  · simp only [canonicalPair, min_eq_left he, max_eq_right he]
    split_ifs <;> rfl
  · have he' := le_of_lt (lt_of_not_ge he)
    simp only [canonicalPair, min_eq_right he', max_eq_left he']
    split_ifs <;> rfl

/-- NEW reconstruction: projecting a matching gives its strict ordered pairing. -/
theorem PerfectMatching.canonicalPair_isPairing (G : MultiGraph V E)
    {M : Finset E} (hM : G.PerfectMatching M) : IsPairing (M.image G.canonicalPair) := by
  classical
  refine ⟨hM.image_edgeMap G (pairGraph V) G.canonicalPair G.canonicalPair_endpointCount, ?_⟩
  intro p hp
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  exact (G.canonicalPair_strict_iff e).2 (hM.no_loop G M e he)


/-- NEW reconstruction: the literal unit sign of an occurrence matching. -/
def matchingPfaffianSign {R : Type*} [CommRing R] (G : MultiGraph V E)
    (orientation : E → Bool) (M : Finset E) : R :=
  (pairingSign (M.image G.canonicalPair) : R) * ∏ e ∈ M, G.canonicalSign orientation e

/-- NEW reconstruction: every occurrence-matching sign squares to one. -/
theorem matchingPfaffianSign_sq {R : Type*} [CommRing R] (G : MultiGraph V E)
    (orientation : E → Bool) (M : Finset E) :
    G.matchingPfaffianSign (R := R) orientation M ^ 2 = 1 := by
  classical
  simp only [matchingPfaffianSign, mul_pow, ← Int.cast_pow, pairingSign_sq,
    Int.cast_one, one_mul, ← Finset.prod_pow, canonicalSign_sq, Finset.prod_const_one]

/-- NEW reconstruction: signs commute with integer coefficient evaluation. -/
theorem matchingPfaffianSign_intCast {R : Type*} [CommRing R] (G : MultiGraph V E)
    (orientation : E → Bool) (M : Finset E) :
    (G.matchingPfaffianSign (R := ℤ) orientation M : R) =
      G.matchingPfaffianSign orientation M := by
  classical
  simp [matchingPfaffianSign, canonicalSign, orientationSign]

/-- NEW reconstruction: constancy of the actual integer matching signs. -/
def IsPfaffianOrientation (G : MultiGraph V E) (orientation : E → Bool) : Prop :=
  ∀ M N, G.PerfectMatching M → G.PerfectMatching N →
    G.matchingPfaffianSign (R := ℤ) orientation M = G.matchingPfaffianSign orientation N

/-- NEW reconstruction: distributing upper fibers gives the exact signed
occurrence-matching sum, retaining parallel edges and permitting zero weights. -/
theorem pairingPfaffian_occurrenceSkewMatrix [Fintype V] [Fintype E]
    {R : Type*} [CommRing R] (G : MultiGraph V E) (orientation : E → Bool) (w : E → R) :
    pairingPfaffian (G.occurrenceSkewMatrix orientation w) =
      ∑ M : {M : Finset E // G.PerfectMatching M},
        G.matchingPfaffianSign orientation M.val * ∏ e ∈ M.val, w e := by
  classical
  let c : Finset (V × V) → R := fun P =>
    if ∀ p ∈ P, p.1 < p.2 then (pairingSign P : R) else 0
  have hstart : pairingPfaffian (G.occurrenceSkewMatrix orientation w) =
      ∑ P : {P : Finset (V × V) // (pairGraph V).PerfectMatching P}, c P.val *
        ∏ p ∈ P.val, ∑ e : {e : E // G.canonicalPair e = p},
          G.canonicalSign orientation e.val * w e.val := by
    unfold pairingPfaffian
    rw [sum_subtype_eq_ite IsPairing
      (fun P => (pairingSign P : R) * ∏ p ∈ P, G.occurrenceSkewMatrix orientation w p.1 p.2),
      sum_subtype_eq_ite (pairGraph V).PerfectMatching
        (fun P => c P * ∏ p ∈ P, ∑ e : {e : E // G.canonicalPair e = p},
          G.canonicalSign orientation e.val * w e.val)]
    apply Finset.sum_congr rfl
    intro P _
    by_cases hP : (pairGraph V).PerfectMatching P
    · by_cases hord : ∀ p ∈ P, p.1 < p.2
      · rw [if_pos ⟨hP,hord⟩, if_pos hP]
        dsimp only [c]
        rw [if_pos hord]
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        rcases p with ⟨u,v⟩
        rw [G.occurrenceSkewMatrix_eq_upperFiberCoefficient orientation w (hord (u,v) hp)]
        unfold upperFiberCoefficient
        apply Finset.sum_congr (by ext; simp)
        intro e _
        rfl
      · rw [if_neg (fun h => hord h.2), if_pos hP]
        dsimp only [c]
        rw [if_neg hord, zero_mul]
    · simp [IsPairing, hP]
  rw [hstart, sum_matching_fiber_products G (pairGraph V) G.canonicalPair
    G.canonicalPair_endpointCount (fun e => G.canonicalSign orientation e * w e) c]
  apply Finset.sum_congr rfl
  intro M _
  have hord := M.property.canonicalPair_isPairing G |>.2
  simp only [c, if_pos hord, Finset.prod_mul_distrib, matchingPfaffianSign]
  ring

/-- NEW reconstruction: a fixed genuine matching calibrates the global sign
without division by a weighted value or a nonvanishing assumption. -/
theorem matchingSum_eq_referenceSign_mul_pairingPfaffian [Fintype V] [Fintype E]
    {R : Type*} [CommRing R] (G : MultiGraph V E) (orientation : E → Bool)
    (ho : G.IsPfaffianOrientation orientation) (M₀ : Finset E)
    (hM₀ : G.PerfectMatching M₀) (w : E → R) :
    (∑ M : {M : Finset E // G.PerfectMatching M}, ∏ e ∈ M.val, w e) =
      G.matchingPfaffianSign orientation M₀ * pairingPfaffian (G.occurrenceSkewMatrix orientation w) := by
  classical
  rw [pairingPfaffian_occurrenceSkewMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  have heq : G.matchingPfaffianSign (R := R) orientation M.val =
      G.matchingPfaffianSign orientation M₀ := by
    simpa only [matchingPfaffianSign_intCast] using
      congrArg (Int.cast : ℤ → R) (ho M.val M₀ M.property hM₀)
  rw [heq, ← mul_assoc, ← pow_two, matchingPfaffianSign_sq, one_mul]

/-- NEW reconstruction: real-valued legacy partition version of calibration. -/
theorem perfectMatchingSum_eq_referenceSign_mul_pairingPfaffian [Fintype V] [Fintype E]
    (G : MultiGraph V E) (orientation : E → Bool) (ho : G.IsPfaffianOrientation orientation)
    (M₀ : Finset E) (hM₀ : G.PerfectMatching M₀) (w : E → ℝ) :
    G.perfectMatchingSum w = G.matchingPfaffianSign orientation M₀ *
      pairingPfaffian (G.occurrenceSkewMatrix orientation w) := by
  classical
  rw [← matchingSum_eq_referenceSign_mul_pairingPfaffian G orientation ho M₀ hM₀ w]
  exact (sum_subtype_eq_ite G.PerfectMatching (fun M => ∏ e ∈ M, w e)).symm

end Canonical
end PlanarHom.MultiGraph
