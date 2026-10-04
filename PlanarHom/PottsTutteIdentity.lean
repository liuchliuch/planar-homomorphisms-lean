import PlanarHom.PottsComponentRank
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# The literal Potts/rank-subset Tutte identity

The polynomial here is defined independently of the partition function by the
standard spanning-edge-subset expansion. The pinned mathlib does not provide a
graph Tutte polynomial (its `SimpleGraph.Tutte` is the perfect-matching theorem).
No deletion–contraction uniqueness theorem or external Tutte complexity
classification is imported or asserted in this file.
-/
noncomputable section
open scoped BigOperators
open Classical

namespace PlanarHom.MultiGraph
variable {V E C R : Type*} [Fintype V] [Fintype E]

/-- Graphic rank of an edge subset, measured on the full original vertex set. -/
def edgeRank (G : MultiGraph V E) (A : Finset E) : ℕ :=
  Fintype.card V - G.componentCount A

/-- The bivariate rank-subset polynomial over the integers. Variable 0 is x,
variable 1 is y. Edge subsets select occurrences, not endpoint pairs. -/
def rankSubsetTuttePolynomial (G : MultiGraph V E) : MvPolynomial (Fin 2) ℤ :=
  ∑ A : Finset E,
    ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) - 1) ^
      (G.edgeRank Finset.univ - G.edgeRank A) *
      ((MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) - 1) ^
        (A.card - G.edgeRank A)

/-- Evaluation of the independent rank-subset polynomial in any commutative ring. -/
def rankSubsetTutte [CommRing R] (G : MultiGraph V E) (x y : R) : R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => if i = 0 then x else y)
    G.rankSubsetTuttePolynomial

theorem rankSubsetTutte_eq_sum [CommRing R] (G : MultiGraph V E) (x y : R) :
    G.rankSubsetTutte x y =
      ∑ A : Finset E, (x - 1) ^ (G.edgeRank Finset.univ - G.edgeRank A) *
        (y - 1) ^ (A.card - G.edgeRank A) := by
  simp [rankSubsetTutte, rankSubsetTuttePolynomial]

theorem rank_difference_eq_components (G : MultiGraph V E) (A : Finset E) :
    G.edgeRank Finset.univ - G.edgeRank A =
      G.componentCount A - G.componentCount Finset.univ := by
  have ha := G.componentCount_le_vertices A
  have he := G.componentCount_le_vertices Finset.univ
  have hm := G.componentCount_antitone (Finset.subset_univ A)
  unfold edgeRank
  omega

omit [Fintype E] in
/-- The cycle exponent is literally |A|-|V|+c(V,A), with the whole
nonnegative integer expression represented in natural arithmetic. -/
theorem cycle_exponent_eq_components (G : MultiGraph V E) (A : Finset E) :
    A.card - G.edgeRank A = A.card + G.componentCount A - Fintype.card V := by
  have hc := G.componentCount_le_vertices A
  have hr := G.vertices_le_card_add_componentCount A
  unfold edgeRank
  omega

/-- Both subtractions in the paper's integer subset expansion are
nonnegative; no truncation changes a rank-subset exponent. -/
theorem component_exponents_nonnegative (G : MultiGraph V E) (A : Finset E) :
    (G.componentCount Finset.univ ≤ G.componentCount A) ∧
      (Fintype.card V ≤ A.card + G.componentCount A) :=
  ⟨G.componentCount_antitone (Finset.subset_univ A),
    G.vertices_le_card_add_componentCount A⟩

/-- The explicit component-count subset formula printed in source §2.7,
Proposition 2.2(ii), including the original isolated vertices. -/
theorem rankSubsetTutte_eq_component_sum [CommRing R] (G : MultiGraph V E) (x y : R) :
    G.rankSubsetTutte x y = ∑ A : Finset E,
      (x - 1) ^ (G.componentCount A - G.componentCount Finset.univ) *
        (y - 1) ^ (A.card + G.componentCount A - Fintype.card V) := by
  simp_rw [rankSubsetTutte_eq_sum, G.rank_difference_eq_components,
    G.cycle_exponent_eq_components]

/-- The exact exponent identity needed to restore the component factor. -/
theorem component_exponent_identity (G : MultiGraph V E) (A : Finset E) :
    G.componentCount Finset.univ +
      (G.edgeRank Finset.univ - G.edgeRank A) = G.componentCount A := by
  rw [G.rank_difference_eq_components]
  exact Nat.add_sub_of_le (G.componentCount_antitone (Finset.subset_univ A))

theorem rankSubsetTutte_potts_point [CommRing R] (G : MultiGraph V E) (q : R) :
    G.rankSubsetTutte (q + 1) 2 =
      ∑ A : Finset E, q ^ (G.componentCount A - G.componentCount Finset.univ) := by
  rw [rankSubsetTutte_eq_sum]
  simp_rw [add_sub_cancel_right, show (2 : R) - 1 = 1 by ring, one_pow, mul_one,
    G.rank_difference_eq_components]

/-- The source's exact `Z_(I+J)(G) = q^c(G) T_G(q+1,2)` formula, with `T`
given by the independent graphic rank-subset polynomial. It is valid also for
q=0 and q=1, the empty graph, loops, parallel occurrences, and isolated vertices. -/
theorem potts_tutte [Fintype C] [CommRing R] (G : MultiGraph V E) :
    G.partition (1 + Matrix.of (fun _ _ => (1 : R)) : Matrix C C R) (fun _ => 1) =
      (Fintype.card C : R) ^ G.componentCount Finset.univ *
        G.rankSubsetTutte ((Fintype.card C : R) + 1) 2 := by
  rw [← pottsInteraction_eq, G.potts_randomCluster, G.rankSubsetTutte_potts_point,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [← pow_add, Nat.add_sub_of_le (G.componentCount_antitone (Finset.subset_univ A))]

/-- Natural color-cardinality specialization without any nonzero hypothesis. -/
theorem potts_tutte_fin [CommRing R] (G : MultiGraph V E) (q : ℕ) :
    G.partition (1 + Matrix.of (fun _ _ => (1 : R)) : Matrix (Fin q) (Fin q) R)
      (fun _ => 1) =
      (q : R) ^ G.componentCount Finset.univ * G.rankSubsetTutte ((q : R) + 1) 2 := by
  convert G.potts_tutte (C := Fin q) (R := R) using 1
  · congr 1
    ext i j
    simp [Matrix.one_apply]
  · simp only [Fintype.card_fin]

end PlanarHom.MultiGraph
