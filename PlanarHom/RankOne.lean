import PlanarHom.Basic

/-!
# Rank-one partition functions

Equation (2.4) of Proposition 2.6 is an identity over every commutative
semiring. A vertex's degree counts both endpoint incidences, so a loop
contributes twice and parallel edges retain their multiplicities.
-/

open scoped BigOperators

namespace PlanarHom
namespace MultiGraph

variable {V E C R : Type*} [Fintype E] [Fintype C]

/-- The incidence degree: the number of source ends plus the number of
destination ends. In particular, each loop contributes two. -/
noncomputable def degree (G : MultiGraph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => G.src e = v)).card +
    (Finset.univ.filter (fun e => G.dst e = v)).card

@[simp] theorem degree_reverse (G : MultiGraph V E) (v : V) :
    G.reverse.degree v = G.degree v := by
  classical
  simp [degree, reverse, Nat.add_comm]

variable [Fintype V] [CommSemiring R]

/-- Regrouping endpoint factors by vertex gives the incidence degree. -/
theorem prod_pow_degree (G : MultiGraph V E) (f : V → R) :
    (∏ v, f v ^ G.degree v) = ∏ e, f (G.src e) * f (G.dst e) := by
  classical
  simp only [degree, pow_add, Finset.prod_mul_distrib]
  congr 1
  · simpa only [Finset.prod_const] using
      (Finset.prod_fiberwise' (Finset.univ : Finset E) G.src f)
  · simpa only [Finset.prod_const] using
      (Finset.prod_fiberwise' (Finset.univ : Finset E) G.dst f)

/-- Weighted rank-one interactions separate into one sum at each vertex. -/
theorem partition_rankOne (G : MultiGraph V E) (a w : C → R) :
    G.partition (fun i j => a i * a j) w =
      ∏ v, ∑ i, w i * a i ^ G.degree v := by
  classical
  unfold partition assignmentWeight
  calc
    (∑ σ : V → C, (∏ v, w (σ v)) * ∏ e, a (σ (G.src e)) * a (σ (G.dst e))) =
        ∑ σ : V → C, ∏ v, w (σ v) * a (σ v) ^ G.degree v := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← G.prod_pow_degree (fun v => a (σ v)), Finset.prod_mul_distrib]
    _ = ∏ v, ∑ i, w i * a i ^ G.degree v :=
      (Fintype.prod_sum (fun v i => w i * a i ^ G.degree v)).symm

/-- Equation (2.4): the unit-background partition function of `a aᵀ`.
No positivity, connectedness, or planarity assumption is required. -/
theorem unweighted_rankOne (G : MultiGraph V E) (a : C → R) :
    G.unweighted (fun i j => a i * a j) =
      ∏ v, ∑ i, a i ^ G.degree v := by
  simpa only [unweighted, one_mul] using G.partition_rankOne a (fun _ => 1)

omit [Fintype V] in
/-- An isolated vertex contributes one for every available color. -/
theorem rankOne_factor_of_degree_zero (G : MultiGraph V E) (a : C → R)
    (v : V) (hv : G.degree v = 0) :
    (∑ i, a i ^ G.degree v) = (Fintype.card C : R) := by
  simp [hv]

end MultiGraph
end PlanarHom
