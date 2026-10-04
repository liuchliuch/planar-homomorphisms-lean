import PlanarHom.FisherPlanarReduction

/-! Concrete output facts needed by the next Pfaffian/FKT stage. These facts
do not assert a Pfaffian orientation or a polynomial-time evaluation oracle. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*}

theorem cubicDecoration_loopless (p : (V × Fin 3) ≃ (E × Bool))
    (e : E ⊕ (V × Fin 3)) : (cubicDecoration p).src e ≠ (cubicDecoration p).dst e := by
  cases e with
  | inl e =>
    intro h
    have hb := congrArg Prod.snd (p.symm.injective h)
    exact Bool.false_ne_true hb
  | inr q =>
    intro h
    exact triangle_distinct_endpoints q.2 (congrArg Prod.snd h)

/-- Every external edge occurrence, and no internal triangle edge. -/
def referenceMatching [Fintype V] [Fintype E] : Finset (E ⊕ (V × Fin 3)) :=
  decoratedEdges Finset.univ (fun _ => ∅)

theorem referenceMatching_perfect [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) : (cubicDecoration p).PerfectMatching referenceMatching := by
  rw [referenceMatching, decorated_perfectMatching_iff]
  intro v
  simp [TriangleCompatible, selectedPorts]

/-- The reference matching has weight exactly one, even when original
edge weights are negative or zero. Its orientation sign can therefore be used
without a search for any nonvanishing matching. -/
theorem referenceMatching_weight [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) :
    (∏ e ∈ referenceMatching, cubicPolynomialWeight p x e) = 1 := by
  simp [referenceMatching, decoratedEdges, internalEdges, cubicPolynomialWeight]

theorem portWeight_two_values (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) (t : ℝ)
    (hx : ∀ e, x e = 1 ∨ x e = t) (q : V × Fin 3) :
    portWeight p x q = 1 ∨ portWeight p x q = t := by
  unfold portWeight
  split_ifs
  · exact Or.inl rfl
  · exact hx _

theorem cubicPolynomialWeight_three_values (p : (V × Fin 3) ≃ (E × Bool)) (x : E → ℝ) (t : ℝ)
    (hx : ∀ e, x e = 1 ∨ x e = t) (e : E ⊕ (V × Fin 3)) :
    cubicPolynomialWeight p x e = 1 ∨ cubicPolynomialWeight p x e = t ∨
      cubicPolynomialWeight p x e = t^2 := by
  cases e with
  | inl e => exact Or.inl rfl
  | inr q =>
    change portWeight p x (q.1, triangle.src q.2) * portWeight p x (q.1, triangle.dst q.2) = 1 ∨ _
    rcases portWeight_two_values p x t hx (q.1, triangle.src q.2) with h | h <;>
      rcases portWeight_two_values p x t hx (q.1, triangle.dst q.2) with h' | h' <;>
        simp [cubicPolynomialWeight,h,h',pow_two]

/-- Uniform zero-field Ising needs only the fixed palette 1, t, t² on the
matching graph. The geometric order introduces no new field constants. -/
theorem fisherWeight_three_values [Fintype V] [Fintype E] {G : MultiGraph V E}
    (o : G.IncidenceOrdering) (t : ℝ)
    (e : ExpansionEdge o ⊕ (ExpansionVertex o × Fin 3)) :
    fisherWeight o (fun _ => t) e = 1 ∨ fisherWeight o (fun _ => t) e = t ∨
      fisherWeight o (fun _ => t) e = t^2 := by
  apply cubicPolynomialWeight_three_values
  intro f
  cases f <;> simp [expansionWeight]

end PlanarHom.Fisher
