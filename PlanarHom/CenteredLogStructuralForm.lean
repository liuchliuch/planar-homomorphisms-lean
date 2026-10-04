import PlanarHom.WeightedStructureTransport
import Mathlib.Tactic.Linarith

/-!
# The structural implication of Lemma 12.4

Membership is in the actual-row-quotient class of Theorem 1.3. No complexity
assumption, hardness negation, or classification oracle enters these results.
All entries and all tensor parameters are arbitrary real numbers.
-/
noncomputable section
open Classical
namespace PlanarHom.CenteredLogStructural
open Boolean Structures
variable {C : Type}

/-- Distinct numerical rows make the canonical actual-row quotient a mere
relabeling, without identifying or discarding any original color. -/
def actualRowEquiv (M : Matrix C C ℝ) (hrows : Function.Injective M) :
    C ≃ Quotient (Twins.rowSetoid M) :=
  Equiv.ofBijective (Quotient.mk (Twins.rowSetoid M)) ⟨by
    intro i j h
    exact hrows (funext (Quotient.exact h)), Quotient.mk_surjective⟩

/-- A singleton actual-row class has exactly its original background weight. -/
theorem quotientWeight_of_injective [Fintype C] (M : Matrix C C ℝ)
    (hrows : Function.Injective M) (w : C → ℝ) (i : C) :
    Twins.quotientWeight M w (Quotient.mk _ i) = w i := by
  let F := {j : C // Quotient.mk (Twins.rowSetoid M) j = Quotient.mk _ i}
  let z : F := ⟨i, rfl⟩
  have hz : ∀ j : F, j = z := by
    intro j
    apply Subtype.ext
    exact hrows (funext (Quotient.exact j.property))
  letI : Unique F := ⟨⟨z⟩, hz⟩
  change (∑ j : F, w j.val) = w i
  simp only [Fintype.sum_unique]
  rfl

/-- Exact simultaneous matrix/weight transport out of the actual quotient. -/
theorem weightedClass_of_actual_membership [Fintype C] (M : Matrix C C ℝ)
    (w : C → ℝ) (hs : ∀ i j, M i j = M j i)
    (hrows : Function.Injective M) (h : PositiveVertexWeightClass M w hs) :
    WeightedClass M w := by
  have ht := h.equiv (actualRowEquiv M hrows)
  have hw : (fun i => Twins.quotientWeight M w (actualRowEquiv M hrows i)) = w := by
    funext i
    exact quotientWeight_of_injective M hrows w i
  change WeightedClass M _ at ht
  rw [hw] at ht
  exact ht

/-- Strict positivity forces every structural block label to be the same. -/
theorem allowedBlock_of_positive [Nonempty C] (M : Matrix C C ℝ) (w : C → ℝ)
    (hpos : ∀ i j, 0 < M i j) (h : WeightedClass M w) :
    AllowedWeightedBlock M w := by
  obtain ⟨t, block, hsurj, hzero, hblocks⟩ := h
  let c : C := Classical.choice inferInstance
  have hb : ∀ i, block i = block c := by
    intro i
    by_contra hi
    exact (ne_of_gt (hpos i c)) (hzero i c hi)
  let e : C ≃ {i // block i = block c} := {
    toFun := fun i => ⟨i, hb i⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (hblocks (block c)).equiv e

/-- The amplitude coordinate disappears: constant diagonal makes every
positive amplitude equal, and distinct rows then permit only one of them. -/
theorem tensor_form_of_allowedBlock [Nonempty C] (M : Matrix C C ℝ) (w : C → ℝ)
    (hpos : ∀ i j, 0 < M i j) (hdiag : ∀ i j, M i i = M j j)
    (hrows : Function.Injective M) (h : AllowedWeightedBlock M w) :
    ∃ (d : ℕ) (e : C ≃ Cube d) (γ μ : ℝ) (ρ : Fin d → ℝ),
      0 < γ ∧ 0 < μ ∧ (∀ r, 0 < ρ r ∧ ρ r ≠ 1) ∧
      (∀ i j, M i j = γ * tensor ρ (e i) (e j)) ∧ (∀ i, w i = μ) := by
  cases h with
  | zero e hM hw =>
    let i := e.symm ()
    exact ((ne_of_gt (hpos i i)) (hM i i)).elim
  | positive k d hk a mass ρ ha hm hρ e hM hw =>
    let z : Cube d := fun _ => false
    let i₀ : Fin k := ⟨0, hk⟩
    have haeq : ∀ i, a i = a i₀ := by
      intro i
      have hd := hdiag (e.symm (i, z)) (e.symm (i₀, z))
      simp only [hM, Equiv.apply_symm_apply, tensor_diag, mul_one] at hd
      have hi := ha i
      have h0 := ha i₀
      nlinarith
    have hieq : ∀ i : Fin k, i = i₀ := by
      intro i
      have hr : M (e.symm (i, z)) = M (e.symm (i₀, z)) := by
        funext j
        simp only [hM, Equiv.apply_symm_apply, haeq i]
      have he := congrArg e (hrows hr)
      simpa only [Equiv.apply_symm_apply, Prod.mk.injEq, and_true] using he
    let ec : C ≃ Cube d := {
      toFun := fun i => (e i).2
      invFun := fun x => e.symm (i₀, x)
      left_inv := fun i => e.injective (by
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext (hieq (e i).1).symm rfl)
      right_inv := fun x => by simp only [Equiv.apply_symm_apply] }
    refine ⟨d, ec, a i₀ * a i₀, mass i₀, ρ, mul_pos (ha _) (ha _), hm _, hρ, ?_, ?_⟩
    · intro i j
      simpa only [ec, haeq] using hM i j
    · intro i
      simpa only [hieq] using hw i
  | bipartite k l d hk hl a massX b massY ρ ha hb hmx hmy hρ e hM hw =>
    let i := e.symm (Sum.inl ⟨0, hk⟩, fun _ => false)
    have hz : M i i = 0 := by
      simp only [hM, i, Equiv.apply_symm_apply, bipartiteAmplitude, zero_mul]
    exact ((ne_of_gt (hpos i i)) hz).elim

/-- Source Lemma 12.4, structural tensor-form conclusion, for arbitrary real
entries and the original actual-row-quotient membership hypothesis. -/
theorem tensor_form_of_structural_membership [Fintype C] [Nonempty C]
    (M : Matrix C C ℝ) (w : C → ℝ)
    (hs : ∀ i j, M i j = M j i) (hpos : ∀ i j, 0 < M i j)
    (hdiag : ∀ i j, M i i = M j j) (hrows : Function.Injective M)
    (hw : ∀ i, 0 < w i) (h : PositiveVertexWeightClass M w hs) :
    ∃ (d : ℕ) (e : C ≃ Cube d) (γ μ : ℝ) (ρ : Fin d → ℝ),
      0 < γ ∧ 0 < μ ∧ (∀ r, 0 < ρ r ∧ ρ r ≠ 1) ∧
      (∀ i j, M i j = γ * tensor ρ (e i) (e j)) ∧ (∀ i, w i = μ) :=
  tensor_form_of_allowedBlock M w hpos hdiag hrows
    (allowedBlock_of_positive M w hpos (weightedClass_of_actual_membership M w hs hrows h))

end PlanarHom.CenteredLogStructural
