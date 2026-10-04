import PlanarHom.Basic
import PlanarHom.Boolean
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp

/-!
# Signed even-subgraph expansion of zero-field Ising

Edges are occurrences of the explicit multigraph edge type. Consequently parallel
edges are selected independently. Degree counts both endpoints of a loop, and
all vertices, including isolated vertices, remain in the spin sum. The expansion
is valid for arbitrary real edge weights, including negative ones. This file
proves a finite polynomial identity; it does not assume or assert an FKT oracle.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph

variable {V E : Type*}

/-- The number of selected endpoint incidences at a vertex. A loop counts twice. -/
def selectedDegree (G : MultiGraph V E) (A : Finset E) (v : V) : ℕ :=
  ∑ e ∈ A, ((if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0))

/-- An even spanning subgraph, with edge multiplicities represented by labels. -/
def EvenSubgraph (G : MultiGraph V E) (A : Finset E) : Prop :=
  ∀ v, Even (G.selectedDegree A v)

/-- The signed weighted sum over all even subsets of edge occurrences. -/
def evenSubgraphSum [Fintype E] (G : MultiGraph V E) (x : E → ℝ) : ℝ :=
  ∑ A : Finset E, if G.EvenSubgraph A then ∏ e ∈ A, x e else 0

/-- The spin associated with a Boolean color. -/
def isingSpin (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem selectedDegree_empty (G : MultiGraph V E) (v : V) :
    G.selectedDegree ∅ v = 0 := by simp [selectedDegree]

@[simp] theorem selectedDegree_insert (G : MultiGraph V E) (A : Finset E)
    (e : E) (he : e ∉ A) (v : V) :
    G.selectedDegree (insert e A) v =
      ((if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0)) +
        G.selectedDegree A v := by simp [selectedDegree, he]

@[simp] theorem evenSubgraph_empty (G : MultiGraph V E) : G.EvenSubgraph ∅ := by
  simp [EvenSubgraph]

theorem prod_single_incidence [Fintype V] (s : V → ℝ) (u : V) :
    (∏ v, s v ^ (if u = v then 1 else 0 : ℕ)) = s u := by
  simp

/-- Regrouping the spin factors by their actual endpoint incidences. -/
theorem prod_spin_endpoints [Fintype V] (G : MultiGraph V E) (A : Finset E)
    (s : V → ℝ) :
    (∏ e ∈ A, s (G.src e) * s (G.dst e)) =
      ∏ v, s v ^ G.selectedDegree A v := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert e A he ih =>
    simp only [Finset.prod_insert he, selectedDegree_insert G A e he,
      pow_add, Finset.prod_mul_distrib, prod_single_incidence, ih]

theorem sum_isingSpin_pow (n : ℕ) :
    (∑ b : Bool, isingSpin b ^ n) = if Even n then 2 else 0 := by
  simp only [Fintype.sum_bool, isingSpin, Bool.false_eq_true, ↓reduceIte, one_pow]
  rw [neg_one_pow_eq_ite]
  split_ifs <;> norm_num

/-- Character cancellation kills precisely the subsets with an odd degree. -/
theorem sum_prod_spin_endpoints [Fintype V] (G : MultiGraph V E) (A : Finset E) :
    (∑ σ : V → Bool, ∏ e ∈ A,
      isingSpin (σ (G.src e)) * isingSpin (σ (G.dst e))) =
      if G.EvenSubgraph A then (2 : ℝ) ^ Fintype.card V else 0 := by
  have hp (σ : V → Bool) := G.prod_spin_endpoints A (fun v => isingSpin (σ v))
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun v (b : Bool) => isingSpin b ^ G.selectedDegree A v)]
  simp_rw [sum_isingSpin_pow]
  by_cases h : G.EvenSubgraph A
  · have hv : ∀ v, Even (G.selectedDegree A v) := h
    simp [h, hv]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)

/-- The multivariate high-temperature identity, with no positivity hypothesis.
The power of two counts every vertex, including every isolated vertex. -/
theorem signed_evenSubgraph_expansion [Fintype V] [Fintype E]
    (G : MultiGraph V E) (x : E → ℝ) :
    (∑ σ : V → Bool, ∏ e,
      (1 + x e * (isingSpin (σ (G.src e)) * isingSpin (σ (G.dst e))))) =
      (2 : ℝ) ^ Fintype.card V * G.evenSubgraphSum x := by
  simp_rw [Finset.prod_one_add]
  rw [Finset.sum_comm]
  have hp (σ : V → Bool) (A : Finset E) :
      (∏ e ∈ A, x e * (isingSpin (σ (G.src e)) * isingSpin (σ (G.dst e)))) =
        (∏ e ∈ A, x e) *
          ∏ e ∈ A, isingSpin (σ (G.src e)) * isingSpin (σ (G.dst e)) :=
    Finset.prod_mul_distrib
  simp_rw [hp, ← Finset.mul_sum]
  simp_rw [G.sum_prod_spin_endpoints]
  simp only [evenSubgraphSum, Finset.mul_sum]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> ring

/-- The two-state interaction factored into its mean and a spin character.
No sign restriction is imposed on the high-temperature parameter. -/
theorem ising_interaction_factor (ρ : ℝ) (hρ : 1 + ρ ≠ 0) (a b : Bool) :
    Boolean.W ρ a b =
      ((1 + ρ) / 2) * (1 + ((1 - ρ) / (1 + ρ)) * (isingSpin a * isingSpin b)) := by
  cases a <;> cases b <;> simp only [Boolean.W, isingSpin, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte] <;> field_simp <;> ring

/-- The paper's exact zero-field Ising even-subgraph expansion. This is valid
even with loops: each selected loop has even incidence degree and contributes
the correct factor in the signed sum. -/
theorem ising_evenSubgraph_expansion [Fintype V] [Fintype E]
    (G : MultiGraph V E) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    G.partition (Boolean.W ρ) (fun _ => 1) =
      (2 : ℝ) ^ Fintype.card V * ((1 + ρ) / 2) ^ Fintype.card E *
        G.evenSubgraphSum (fun _ => (1 - ρ) / (1 + ρ)) := by
  simp only [partition, assignmentWeight_one]
  simp_rw [ising_interaction_factor ρ hρ]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Finset.mul_sum]
  rw [G.signed_evenSubgraph_expansion]
  ring

/-- Constant edge weights reduce the monomial to the cardinality of the actual
selected occurrence set, not the number of distinct endpoint pairs. -/
theorem evenSubgraphSum_const [Fintype E] (G : MultiGraph V E) (t : ℝ) :
    G.evenSubgraphSum (fun _ => t) =
      ∑ A : Finset E, if G.EvenSubgraph A then t ^ A.card else 0 := by
  simp [evenSubgraphSum]

/-- The normalization as printed in Section 2.8; positivity is used only to
ensure the denominator is nonzero. Negative summands for `ρ > 1` are retained. -/
theorem ising_evenSubgraph_expansion_pos [Fintype V] [Fintype E]
    (G : MultiGraph V E) (ρ : ℝ) (hρ : 0 < ρ) :
    G.partition (Boolean.W ρ) (fun _ => 1) =
      (2 : ℝ) ^ Fintype.card V * ((1 + ρ) / 2) ^ Fintype.card E *
        ∑ A : Finset E, if G.EvenSubgraph A then ((1 - ρ) / (1 + ρ)) ^ A.card else 0 := by
  rw [G.ising_evenSubgraph_expansion ρ (ne_of_gt (add_pos zero_lt_one hρ))]
  rw [G.evenSubgraphSum_const]

end PlanarHom.MultiGraph
