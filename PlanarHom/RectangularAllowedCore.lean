import PlanarHom.RectangularUnitCoreSource
import PlanarHom.MainStructuralSupportTransport

/-! NEW: a positive rectangular double is one allowed support block, and
absence of proportional rows removes repeated amplitude coordinates. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularBooleanCore
open Structures Boolean BipartiteFullTwins

variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem allowed_double (C : Matrix X Y ℝ) (hp : ∀ x y, 0 < C x y)
    (hc : NonnegativeClass (double C)) : AllowedBlock (double C) := by
  obtain ⟨t, block, _, hz, hblock⟩ := hc
  let x0 : X := Classical.arbitrary X
  let y0 : Y := Classical.arbitrary Y
  have hcross (x : X) (y : Y) : block (.inl x) = block (.inr y) := by
    by_contra h
    exact (ne_of_gt (hp x y)) (hz _ _ h)
  have hall (z : X ⊕ Y) : block z = block (.inl x0) := by
    cases z with
    | inl x => exact (hcross x y0).trans (hcross x0 y0).symm
    | inr y => exact (hcross x0 y).symm
  let e : (X ⊕ Y) ≃ {z // block z = block (.inl x0)} :=
    { toFun := fun z => ⟨z, hall z⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (hblock (block (.inl x0))).equiv e

theorem double_nonproportional (C : Matrix X Y ℝ) (hp : ∀ x y, 0 < C x y)
    (hrows : ∀ x x', x ≠ x' → ∀ t : ℝ, C x ≠ t • C x')
    (hcols : ∀ y y', y ≠ y' → ∀ t : ℝ, C.transpose y ≠ t • C.transpose y') :
    ∀ u v, u ≠ v → ∀ t : ℝ, double C u ≠ t • double C v := by
  apply RectangularUnitCoreSource.double_rows_nonproportional C hp
  · intro x x' t he
    by_contra hn
    exact hrows x x' hn t (funext he)
  · intro y y' t he
    by_contra hn
    exact hcols y y' hn t (funext he)

theorem bipartite_amplitude_sizes {Z : Type} {M : Matrix Z Z ℝ}
    (h : ∀ u v, u ≠ v → ∀ t : ℝ, M u ≠ t • M v)
    {k l d : ℕ} (hk : 0 < k) (hl : 0 < l)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (ρ : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (e : Z ≃ (Fin k ⊕ Fin l) × Cube d)
    (hm : ∀ i j, M i j = bipartiteAmplitude a b (e i).1 (e j).1 *
      tensor ρ (e i).2 (e j).2) : k = 1 ∧ l = 1 := by
  have hi : ∀ i j : Fin k, i = j := by
    intro i j
    let x : Cube d := fun _ => false
    have he : e.symm (.inl i, x) = e.symm (.inl j, x) := by
      by_contra hn
      apply h _ _ hn (a i / a j)
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hm, Equiv.apply_symm_apply]
      cases (e v).1 <;> simp only [bipartiteAmplitude]
      · ring
      · field_simp [ne_of_gt (ha j)]
    exact Sum.inl.inj (congrArg Prod.fst (e.symm.injective he))
  have hj : ∀ i j : Fin l, i = j := by
    intro i j
    let x : Cube d := fun _ => false
    have he : e.symm (.inr i, x) = e.symm (.inr j, x) := by
      by_contra hn
      apply h _ _ hn (b i / b j)
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hm, Equiv.apply_symm_apply]
      cases (e v).1 <;> simp only [bipartiteAmplitude]
      · field_simp [ne_of_gt (hb j)]
        <;> ring
      · ring
    exact Sum.inr.inj (congrArg Prod.fst (e.symm.injective he))
  constructor
  · by_contra hn
    have h2 : 1 < k := by omega
    have he := congrArg Fin.val (hi ⟨0, hk⟩ ⟨1, h2⟩)
    simp at he
  · by_contra hn
    have h2 : 1 < l := by omega
    have he := congrArg Fin.val (hj ⟨0, hl⟩ ⟨1, h2⟩)
    simp at he

theorem double_bipartite_chart (C : Matrix X Y ℝ) (hp : ∀ x y, 0 < C x y)
    (hn : ∀ u v, u ≠ v → ∀ t : ℝ, double C u ≠ t • double C v)
    (hc : NonnegativeClass (double C)) :
    ∃ d, ∃ a b : Fin 1 → ℝ, ∃ ρ : Fin d → ℝ,
      (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧ (∀ r, 0 < ρ r) ∧
      ∃ e : (X ⊕ Y) ≃ (Fin 1 ⊕ Fin 1) × Cube d,
      ∀ i j, double C i j = bipartiteAmplitude a b (e i).1 (e j).1 *
        tensor ρ (e i).2 (e j).2 := by
  have h := allowed_double C hp hc
  cases h with
  | zero e hz =>
    exact False.elim ((ne_of_gt (hp (Classical.arbitrary X) (Classical.arbitrary Y)))
      (hz (.inl (Classical.arbitrary X)) (.inr (Classical.arbitrary Y))))
  | positive k d hk a ρ ha hρ e hm =>
    let z : X ⊕ Y := .inl (Classical.arbitrary X)
    have he := hm z z
    have hz : double C z z = 0 := rfl
    rw [hz, tensor_diag, mul_one] at he
    exact False.elim ((ne_of_gt (mul_pos (ha _) (ha _))) he.symm)
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    obtain ⟨hk1, hl1⟩ := bipartite_amplitude_sizes hn hk hl a b ρ ha hb e hm
    subst k
    subst l
    exact ⟨d, a, b, ρ, ha, hb, hρ, e, hm⟩

end PlanarHom.RectangularBooleanCore
