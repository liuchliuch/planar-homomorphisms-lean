import PlanarHom.FisherCubicDecoration

/-! The signed weighted perfect-matching identity for the explicit cubic
Fisher decoration. No planarity or algorithmic oracle is assumed. -/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph
variable {V E : Type*}

theorem evenSubgraphSum_eq_subtype [Fintype E] (G : MultiGraph V E) (x : E → ℝ) :
    G.evenSubgraphSum x =
      ∑ A : {A : Finset E // G.EvenSubgraph A}, ∏ e ∈ A.1, x e := by
  rw [evenSubgraphSum, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem perfectMatchingSum_eq_subtype [Fintype E] (G : MultiGraph V E) (w : E → ℝ) :
    G.perfectMatchingSum w =
      ∑ M : {M : Finset E // G.PerfectMatching M}, ∏ e ∈ M.1, w e := by
  rw [perfectMatchingSum, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end PlanarHom.MultiGraph

namespace PlanarHom.Fisher
variable {V E : Type*}

/-- External occurrences receive reciprocal weights; every triangle edge has
weight one. The separate product of original weights restores the monomial. -/
def cubicWeight (x : E → ℝ) : E ⊕ (V × Fin 3) → ℝ :=
  Sum.elim (fun e => (x e)⁻¹) (fun _ => 1)

theorem prod_cubicWeight [Fintype V] (x : E → ℝ)
    (B : Finset E) (m : V → Finset (Fin 3)) :
    (∏ e ∈ decoratedEdges B m, cubicWeight x e) = ∏ e ∈ B, (x e)⁻¹ := by
  simp [decoratedEdges, Finset.prod_disjSum, cubicWeight]

/-- The actual weighted Fisher identity for a cubic incidence presentation.
Nonzero weights may be negative; no positivity or Pfaffian hypothesis occurs. -/
theorem cubic_fisher_weighted [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) (hx : ∀ e, x e ≠ 0) :
    (cubicOriginal p).evenSubgraphSum x =
      (∏ e, x e) * (cubicDecoration p).perfectMatchingSum (cubicWeight x) := by
  rw [MultiGraph.evenSubgraphSum_eq_subtype, MultiGraph.perfectMatchingSum_eq_subtype,
    Finset.mul_sum]
  apply Fintype.sum_equiv (cubicFisherEquiv p)
  intro A
  change (∏ e ∈ A.1, x e) = (∏ e, x e) *
    ∏ e ∈ decoratedEdges A.1ᶜ
      (fun v => triangleCompletion (selectedPorts p A.1ᶜ v)), cubicWeight x e
  rw [prod_cubicWeight, ← Finset.prod_mul_prod_compl A.1 x, Finset.prod_inv_distrib]
  rw [mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun e _ => hx e)), mul_one]

/-- Put an original edge's full weight at its source port and weight one at
its target port. These are distinct endpoint occurrences even for a loop. -/
def portWeight (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) (q : V × Fin 3) : ℝ :=
  if (p q).2 then 1 else x (p q).1

/-- A polynomial weight assignment: external edges have weight one, while an
internal triangle edge receives the product of its two port weights. -/
def cubicPolynomialWeight (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) :
    E ⊕ (V × Fin 3) → ℝ :=
  Sum.elim (fun _ => 1) (fun q =>
    portWeight p x (q.1, triangle.src q.2) * portWeight p x (q.1, triangle.dst q.2))

theorem triangle_matching_weight (s : Fin 3 → ℝ) (B M : Finset (Fin 3))
    (h : TriangleCompatible B M) :
    (∏ e ∈ M, s (triangle.src e) * s (triangle.dst e)) =
      ∏ i, if i ∈ B then 1 else s i := by
  rw [triangle.prod_spin_endpoints M s]
  apply Finset.prod_congr rfl
  intro i _
  have hd := (triangleCompatible_iff_degree B M).mp h i
  by_cases hi : i ∈ B
  · have hzero : triangle.selectedDegree M i = 0 := by simpa [hi] using hd
    simp [hi, hzero]
  · have hone : triangle.selectedDegree M i = 1 := by simpa [hi] using hd
    simp [hi, hone]

theorem prod_polynomialWeight [Fintype V]
    (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ)
    (B : Finset E) (m : V → Finset (Fin 3))
    (hm : ∀ v, TriangleCompatible (selectedPorts p B v) (m v)) :
    (∏ e ∈ decoratedEdges B m, cubicPolynomialWeight p x e) =
      ∏ q : V × Fin 3, if (p q).1 ∈ B then 1 else portWeight p x q := by
  calc
    _ = ∏ v, ∏ i ∈ m v,
        portWeight p x (v, triangle.src i) * portWeight p x (v, triangle.dst i) := by
      simp [decoratedEdges, cubicPolynomialWeight, Finset.prod_disjSum,
        internalEdges, Finset.prod_filter, Fintype.prod_prod_type]
    _ = ∏ v, ∏ i : Fin 3,
        if i ∈ selectedPorts p B v then 1 else portWeight p x (v, i) := by
      apply Finset.prod_congr rfl
      intro v _
      exact triangle_matching_weight (fun i => portWeight p x (v, i))
        (selectedPorts p B v) (m v) (hm v)
    _ = _ := by simp [Fintype.prod_prod_type, selectedPorts]

theorem prod_complement_portWeight [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) (A : Finset E) :
    (∏ q : V × Fin 3, if (p q).1 ∈ Aᶜ then 1 else portWeight p x q) =
      ∏ e ∈ A, x e := by
  calc
    _ = ∏ d : E × Bool, if d.1 ∈ Aᶜ then 1 else (if d.2 then 1 else x d.1) := by
      apply Fintype.prod_equiv p
      intro q
      rfl
    _ = _ := by
      rw [Fintype.prod_prod_type]
      simp only [Fintype.prod_bool]
      simp

/-- Fisher's correspondence as a literal polynomial matching identity.
Every real edge weight is allowed, including zero and negative values. -/
theorem cubic_fisher_polynomial [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) :
    (cubicOriginal p).evenSubgraphSum x =
      (cubicDecoration p).perfectMatchingSum (cubicPolynomialWeight p x) := by
  rw [MultiGraph.evenSubgraphSum_eq_subtype, MultiGraph.perfectMatchingSum_eq_subtype]
  apply Fintype.sum_equiv (cubicFisherEquiv p)
  intro A
  change (∏ e ∈ A.1, x e) = ∏ e ∈ decoratedEdges A.1ᶜ
    (fun v => triangleCompletion (selectedPorts p A.1ᶜ v)), cubicPolynomialWeight p x e
  rw [prod_polynomialWeight]
  · exact (prod_complement_portWeight p x A.1).symm
  · apply (decorated_perfectMatching_iff p A.1ᶜ _).mp
    exact (cubic_matching_completion_iff p A.1 _).mpr ⟨A.2, rfl⟩

/-- Composition with the genuine Ising expansion, retaining all scalar factors.
This remains a combinatorial identity, without a planarity or FP assertion. -/
theorem cubic_ising_matching [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    (cubicOriginal p).partition (Boolean.W ρ) (fun _ => 1) =
      (2 : ℝ) ^ Fintype.card V * ((1 + ρ) / 2) ^ Fintype.card E *
        (cubicDecoration p).perfectMatchingSum
          (cubicPolynomialWeight p (fun _ => (1 - ρ) / (1 + ρ))) := by
  rw [MultiGraph.ising_evenSubgraph_expansion _ ρ hρ, cubic_fisher_polynomial]

theorem cubicDecoration_vertexCount [Fintype V] :
    Fintype.card (V × Fin 3) = 3 * Fintype.card V := by
  simp [Fintype.card_prod, Nat.mul_comm]

theorem cubicDecoration_edgeCount [Fintype V] [Fintype E] :
    Fintype.card (E ⊕ (V × Fin 3)) = Fintype.card E + 3 * Fintype.card V := by
  simp [Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]

end PlanarHom.Fisher
