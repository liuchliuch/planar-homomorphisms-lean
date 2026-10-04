import PlanarHom.Boolean
import PlanarHom.Quotient
import Mathlib.Tactic.Positivity

/-!
# Structural classes appearing in the main dichotomies

This file specifies the matrix and aggregated-weight conditions of Theorems 1.1
and 1.3. The complexity dichotomies are proved in `MainDichotomiesClosed`. Block membership
is a concrete algebraic predicate, not an axiom about a counting problem.
-/

open Classical
noncomputable section

namespace PlanarHom.Structures

variable {C : Type*}

/-- The cross interaction of a bipartite rank-two block. -/
def bipartiteAmplitude {k l : ℕ} (a : Fin k → ℝ) (b : Fin l → ℝ) :
    (Fin k ⊕ Fin l) → (Fin k ⊕ Fin l) → ℝ
  | .inl i, .inr j => a i * b j
  | .inr j, .inl i => a i * b j
  | _, _ => 0

theorem bipartiteAmplitude_symm {k l : ℕ} (a : Fin k → ℝ) (b : Fin l → ℝ)
    (i j : Fin k ⊕ Fin l) : bipartiteAmplitude a b i j = bipartiteAmplitude a b j i := by
  cases i <;> cases j <;> rfl

theorem bipartiteAmplitude_nonneg {k l : ℕ} {a : Fin k → ℝ} {b : Fin l → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (i j : Fin k ⊕ Fin l) :
    0 ≤ bipartiteAmplitude a b i j := by
  cases i <;> cases j <;> simp only [bipartiteAmplitude]
  · exact le_rfl
  · exact mul_nonneg (ha _) (hb _)
  · exact mul_nonneg (ha _) (hb _)
  · exact le_rfl

/-- One support block in Theorem 1.1, in arbitrary color coordinates. -/
inductive AllowedBlock (M : Matrix C C ℝ) : Prop
  | zero (e : C ≃ Unit) (hM : ∀ i j, M i j = 0) : AllowedBlock M
  | positive (k d : ℕ) (hk : 0 < k)
      (a : Fin k → ℝ) (ρ : Fin d → ℝ)
      (ha : ∀ i, 0 < a i) (hρ : ∀ r, 0 < ρ r)
      (e : C ≃ Fin k × Boolean.Cube d)
      (hM : ∀ i j, M i j = a (e i).1 * a (e j).1 * Boolean.tensor ρ (e i).2 (e j).2) :
      AllowedBlock M
  | bipartite (k l d : ℕ) (hk : 0 < k) (hl : 0 < l)
      (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ)
      (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hρ : ∀ r, 0 < ρ r)
      (e : C ≃ (Fin k ⊕ Fin l) × Boolean.Cube d)
      (hM : ∀ i j, M i j = bipartiteAmplitude a b (e i).1 (e j).1 *
        Boolean.tensor ρ (e i).2 (e j).2) : AllowedBlock M

/-- The whole direct-sum structural condition of Theorem 1.1. -/
def NonnegativeClass (M : Matrix C C ℝ) : Prop :=
  ∃ (t : ℕ) (block : C → Fin t), Function.Surjective block ∧
    (∀ i j, block i ≠ block j → M i j = 0) ∧
    ∀ r, AllowedBlock (fun i j : {c // block c = r} => M i.1 j.1)

theorem AllowedBlock.symmetric {M : Matrix C C ℝ} (h : AllowedBlock M) :
    ∀ i j, M i j = M j i := by
  cases h with
  | zero e hM => intro i j; rw [hM, hM]
  | positive k d hk a ρ ha hρ e hM =>
    intro i j
    rw [hM, hM, Boolean.tensor_symm ρ (e i).2 (e j).2]
    ring
  | bipartite k l d hk hl a b ρ ha hb hρ e hM =>
    intro i j
    rw [hM, hM, bipartiteAmplitude_symm a b (e i).1 (e j).1,
      Boolean.tensor_symm ρ (e i).2 (e j).2]

theorem AllowedBlock.nonnegative {M : Matrix C C ℝ} (h : AllowedBlock M) :
    ∀ i j, 0 ≤ M i j := by
  cases h with
  | zero e hM => intro i j; rw [hM]
  | positive k d hk a ρ ha hρ e hM =>
    intro i j
    rw [hM]
    exact mul_nonneg (mul_nonneg (ha _).le (ha _).le) (Boolean.tensor_pos hρ _ _).le
  | bipartite k l d hk hl a b ρ ha hb hρ e hM =>
    intro i j
    rw [hM]
    exact mul_nonneg
      (bipartiteAmplitude_nonneg (fun i => (ha i).le) (fun j => (hb j).le) _ _)
      (Boolean.tensor_pos hρ _ _).le

/-- One quotient support block in Theorem 1.3. Nondegenerate Ising factors
have parameter different from one. -/
inductive AllowedWeightedBlock (M : Matrix C C ℝ) (w : C → ℝ) : Prop
  | zero (e : C ≃ Unit) (hM : ∀ i j, M i j = 0) (hw : ∀ i, 0 < w i) :
      AllowedWeightedBlock M w
  | positive (k d : ℕ) (hk : 0 < k)
      (a mass : Fin k → ℝ) (ρ : Fin d → ℝ)
      (ha : ∀ i, 0 < a i) (hmass : ∀ i, 0 < mass i)
      (hρ : ∀ r, 0 < ρ r ∧ ρ r ≠ 1)
      (e : C ≃ Fin k × Boolean.Cube d)
      (hM : ∀ i j, M i j = a (e i).1 * a (e j).1 * Boolean.tensor ρ (e i).2 (e j).2)
      (hw : ∀ i, w i = mass (e i).1) : AllowedWeightedBlock M w
  | bipartite (k l d : ℕ) (hk : 0 < k) (hl : 0 < l)
      (a massX : Fin k → ℝ) (b massY : Fin l → ℝ) (ρ : Fin d → ℝ)
      (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
      (hmassX : ∀ i, 0 < massX i) (hmassY : ∀ j, 0 < massY j)
      (hρ : ∀ r, 0 < ρ r ∧ ρ r ≠ 1)
      (e : C ≃ (Fin k ⊕ Fin l) × Boolean.Cube d)
      (hM : ∀ i j, M i j = bipartiteAmplitude a b (e i).1 (e j).1 *
        Boolean.tensor ρ (e i).2 (e j).2)
      (hw : ∀ i, w i = Sum.elim massX massY (e i).1) : AllowedWeightedBlock M w

/-- Direct-sum weighted form, applied to the actual-row quotient in Theorem 1.3. -/
def WeightedClass (M : Matrix C C ℝ) (w : C → ℝ) : Prop :=
  ∃ (t : ℕ) (block : C → Fin t), Function.Surjective block ∧
    (∀ i j, block i ≠ block j → M i j = 0) ∧
    ∀ r, AllowedWeightedBlock (fun i j : {c // block c = r} => M i.1 j.1)
      (fun i => w i.1)

/-- The structural condition of Theorem 1.3 includes forming the original
actual-row quotient first, rather than testing the microscopic weights directly. -/
def PositiveVertexWeightClass [Fintype C] (M : Matrix C C ℝ) (w : C → ℝ)
    (hM : ∀ i j, M i j = M j i) : Prop :=
  WeightedClass (Twins.quotientMatrix M hM) (Twins.quotientWeight M w)

/-- Forgetting the permitted positive vertex weights gives an unweighted block. -/
theorem AllowedWeightedBlock.unweighted {M : Matrix C C ℝ} {w : C → ℝ}
    (h : AllowedWeightedBlock M w) : AllowedBlock M := by
  cases h with
  | zero e hM hw => exact .zero e hM
  | positive k d hk a mass ρ ha hmass hρ e hM hw =>
    exact .positive k d hk a ρ ha (fun r => (hρ r).1) e hM
  | bipartite k l d hk hl a massX b massY ρ ha hb hmassX hmassY hρ e hM hw =>
    exact .bipartite k l d hk hl a b ρ ha hb (fun r => (hρ r).1) e hM

/-- Every listed weighted block has strictly positive vertex weights. -/
theorem AllowedWeightedBlock.positive_weights {M : Matrix C C ℝ} {w : C → ℝ}
    (h : AllowedWeightedBlock M w) : ∀ i, 0 < w i := by
  cases h with
  | zero e hM hw => exact hw
  | positive k d hk a mass ρ ha hmass hρ e hM hw =>
    intro i
    rw [hw]
    exact hmass _
  | bipartite k l d hk hl a massX b massY ρ ha hb hmassX hmassY hρ e hM hw =>
    intro i
    rw [hw]
    cases hside : (e i).1 with
    | inl j => exact hmassX j
    | inr j => exact hmassY j

/-- The direct-sum structural condition entails symmetry. -/
theorem NonnegativeClass.symmetric {M : Matrix C C ℝ} (h : NonnegativeClass M) :
    ∀ i j, M i j = M j i := by
  obtain ⟨t, block, hsurj, hzero, hblocks⟩ := h
  intro i j
  by_cases he : block i = block j
  · exact (hblocks (block i)).symmetric ⟨i, rfl⟩ ⟨j, he.symm⟩
  · rw [hzero i j he, hzero j i (Ne.symm he)]

/-- The direct-sum structural condition entails entrywise nonnegativity. -/
theorem NonnegativeClass.nonnegative {M : Matrix C C ℝ} (h : NonnegativeClass M) :
    ∀ i j, 0 ≤ M i j := by
  obtain ⟨t, block, hsurj, hzero, hblocks⟩ := h
  intro i j
  by_cases he : block i = block j
  · exact (hblocks (block i)).nonnegative ⟨i, rfl⟩ ⟨j, he.symm⟩
  · rw [hzero i j he]

/-- Forgetting permitted weights preserves the main unweighted structure. -/
theorem WeightedClass.unweighted {M : Matrix C C ℝ} {w : C → ℝ}
    (h : WeightedClass M w) : NonnegativeClass M := by
  obtain ⟨t, block, hsurj, hzero, hblocks⟩ := h
  exact ⟨t, block, hsurj, hzero, fun r => (hblocks r).unweighted⟩

end PlanarHom.Structures
