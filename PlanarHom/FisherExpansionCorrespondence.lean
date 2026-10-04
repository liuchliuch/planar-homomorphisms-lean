import PlanarHom.FisherExpansionGraph

/-! Full occurrence-set equivalence and weighted factor for arbitrary-degree
cubic expansion. No plane-embedding compatibility is assumed in this algebra. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

def readExpansionInternal (o : IncidenceOrdering G) (M : Finset (ExpansionEdge o))
    (v : V) : Finset (Fin (o.degree v + 1) ⊕ Bool) :=
  Finset.univ.filter (fun e => Sum.inr (⟨v, e⟩ : ExpansionInternalEdge o) ∈ M)

@[simp] theorem expansionSet_toLeft [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) :
    (expansionSet o A m).toLeft = A := by simp [expansionSet]

@[simp] theorem readExpansionInternal_set [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) :
    readExpansionInternal o (expansionSet o A m) = m := by
  funext v
  ext e
  simp [readExpansionInternal, expansionSet, expansionInternalSet]

theorem expansionSet_read [Fintype V] (o : IncidenceOrdering G) (M : Finset (ExpansionEdge o)) :
    expansionSet o M.toLeft (readExpansionInternal o M) = M := by
  ext e
  cases e <;> simp [readExpansionInternal, expansionSet, expansionInternalSet]

/-- Canonical forced paths, with the two endpoint-loop choices supplied freely. -/
def canonicalExpansionSet [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (L : V → Finset Bool) : Finset (ExpansionEdge o) :=
  expansionSet o A (fun v => (parityEdges (o.portBits A v)).disjSum (L v))

theorem canonicalExpansionSet_even [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (A : Finset E) (L : V → Finset Bool) (hA : G.EvenSubgraph A) :
    (expansionGraph o).EvenSubgraph (canonicalExpansionSet o A L) :=
  (expansion_even_iff o A _ L).mpr ⟨hA, fun _ => rfl⟩

theorem expanded_even_read [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (M : Finset (ExpansionEdge o))
    (hM : (expansionGraph o).EvenSubgraph M) :
    G.EvenSubgraph M.toLeft ∧
      ∀ v, (readExpansionInternal o M v).toLeft = parityEdges (o.portBits M.toLeft v) := by
  apply (expansion_even_iff o M.toLeft
    (fun v => (readExpansionInternal o M v).toLeft)
    (fun v => (readExpansionInternal o M v).toRight)).mp
  simpa only [Finset.toLeft_disjSum_toRight, expansionSet_read] using hM

theorem canonicalExpansionSet_read [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (M : Finset (ExpansionEdge o))
    (hM : (expansionGraph o).EvenSubgraph M) :
    canonicalExpansionSet o M.toLeft (fun v => (readExpansionInternal o M v).toRight) = M := by
  unfold canonicalExpansionSet
  have hm := (expanded_even_read o M hM).2
  simp_rw [← hm, Finset.toLeft_disjSum_toRight]
  exact expansionSet_read o M

/-- Exact arbitrary-degree correspondence. Each original even subgraph has
four independent loop choices per original vertex, even when it is isolated. -/
def expansionEvenEquiv [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    ({A : Finset E // G.EvenSubgraph A} × (V → Finset Bool)) ≃
      {M : Finset (ExpansionEdge o) // (expansionGraph o).EvenSubgraph M} where
  toFun s := ⟨canonicalExpansionSet o s.1.1 s.2, canonicalExpansionSet_even o _ _ s.1.2⟩
  invFun M := (⟨M.1.toLeft, (expanded_even_read o M.1 M.2).1⟩,
    fun v => (readExpansionInternal o M.1 v).toRight)
  left_inv s := by
    apply Prod.ext
    · apply Subtype.ext
      simp [canonicalExpansionSet]
    · funext v
      simp [canonicalExpansionSet]
  right_inv M := Subtype.ext (canonicalExpansionSet_read o M.1 M.2)

/-- All new path and loop edges have weight one. -/
def expansionWeight (o : IncidenceOrdering G) (x : E → ℝ) : ExpansionEdge o → ℝ :=
  Sum.elim x (fun _ => 1)

theorem prod_expansionWeight [Fintype V] (o : IncidenceOrdering G) (x : E → ℝ)
    (A : Finset E) (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) :
    (∏ e ∈ expansionSet o A m, expansionWeight o x e) = ∏ e ∈ A, x e := by
  simp [expansionSet, expansionWeight, Finset.prod_disjSum]

/-- Polynomial identity with the precise multiplicity of the two free loops
at every original vertex. Original weights may have any signs or be zero. -/
theorem expansion_evenSubgraphSum [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (x : E → ℝ) :
    (expansionGraph o).evenSubgraphSum (expansionWeight o x) =
      (4 : ℝ) ^ Fintype.card V * G.evenSubgraphSum x := by
  rw [MultiGraph.evenSubgraphSum_eq_subtype, MultiGraph.evenSubgraphSum_eq_subtype]
  calc
    _ = ∑ s : ({A : Finset E // G.EvenSubgraph A} × (V → Finset Bool)),
        ∏ e ∈ s.1.1, x e := by
      symm
      apply Fintype.sum_equiv (expansionEvenEquiv o)
      intro s
      exact (prod_expansionWeight o x s.1.1 _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [Fintype.card_finset, ← Finset.mul_sum]

/-- An ordinary weighted perfect-matching sum for every ordered input graph.
The graph and all its weights are explicit; planarity is a separate theorem. -/
theorem arbitrary_fisher_polynomial [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (x : E → ℝ) :
    (cubicDecoration (expansionCubicPorts o)).perfectMatchingSum
        (cubicPolynomialWeight (expansionCubicPorts o) (expansionWeight o x)) =
      (4 : ℝ) ^ Fintype.card V * G.evenSubgraphSum x := by
  rw [← cubic_fisher_polynomial, cubicOriginal_expansionCubicPorts, expansion_evenSubgraphSum]

/-- The complete arbitrary-input finite Ising-to-matching identity. The
normalization includes isolates and the exact extra-loop multiplicity. -/
theorem arbitrary_ising_matching [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    G.partition (Boolean.W ρ) (fun _ => 1) =
      (((1 + ρ) / 2) ^ Fintype.card E / (2 : ℝ) ^ Fintype.card V) *
        (cubicDecoration (expansionCubicPorts o)).perfectMatchingSum
          (cubicPolynomialWeight (expansionCubicPorts o)
            (expansionWeight o (fun _ => (1 - ρ) / (1 + ρ)))) := by
  rw [arbitrary_fisher_polynomial, G.ising_evenSubgraph_expansion ρ hρ]
  have hpow : (4 : ℝ) ^ Fintype.card V = (2 ^ Fintype.card V) * (2 ^ Fintype.card V) := by
    rw [← mul_pow]
    norm_num
  rw [hpow]
  have hn : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem evenSubgraphSum_zero [Fintype E] (G : MultiGraph V E) :
    G.evenSubgraphSum (fun _ => 0) = 1 := by
  unfold MultiGraph.evenSubgraphSum
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro A _ hA
    split_ifs
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      exact Finset.prod_eq_zero he rfl
    · rfl
  · simp

theorem sum_incidence_degree [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    (∑ v, o.degree v) = 2 * Fintype.card E := by
  simpa [Fintype.card_sigma, Fintype.card_prod, Nat.mul_comm] using Fintype.card_congr o.darts

theorem expansion_vertexCount [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    Fintype.card (ExpansionVertex o) = 2 * (Fintype.card E + Fintype.card V) := by
  simp only [ExpansionVertex, Fintype.card_sigma, Fintype.card_fin,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [sum_incidence_degree]
  omega

theorem expansion_edgeCount [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    Fintype.card (ExpansionEdge o) = 3 * (Fintype.card E + Fintype.card V) := by
  simp only [ExpansionEdge, ExpansionInternalEdge, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, Fintype.card_bool, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [sum_incidence_degree]
  omega

end PlanarHom.Fisher
