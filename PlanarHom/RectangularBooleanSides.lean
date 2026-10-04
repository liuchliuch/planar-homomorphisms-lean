import PlanarHom.RectangularAllowedCore

/-! NEW: the two source sides of a positive rectangular double inherit the
same Boolean cube, even when the global allowed-block chart swaps sides. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularBooleanCore
open Structures Boolean BipartiteFullTwins

def unitSides : (Fin 1 ⊕ Fin 1) ≃ Bool where
  toFun := Sum.elim (fun _ => false) (fun _ => true)
  invFun := fun b => if b then .inr 0 else .inl 0
  left_inv := by intro a; cases a <;> simp [Subsingleton.elim (α := Fin 1) _ 0]
  right_inv := by intro b; cases b <;> rfl

theorem amplitude_unit (a b : Fin 1 → ℝ) (u v : Fin 1 ⊕ Fin 1) :
    bipartiteAmplitude a b u v =
      if unitSides u = unitSides v then 0 else a 0 * b 0 := by
  cases u <;> cases v <;>
    simp [bipartiteAmplitude, unitSides, Subsingleton.elim (α := Fin 1) _ 0]

theorem split_bool_chart {X Y T : Type} [Nonempty X] [Nonempty Y]
    (e : (X ⊕ Y) ≃ Bool × T)
    (hcross : ∀ x y, (e (.inl x)).1 ≠ (e (.inr y)).1) :
    ∃ eX : X ≃ T, ∃ eY : Y ≃ T,
      (∀ x, eX x = (e (.inl x)).2) ∧ (∀ y, eY y = (e (.inr y)).2) := by
  let x0 : X := Classical.arbitrary X
  let y0 : Y := Classical.arbitrary Y
  have bool_unique (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a = b := by
    cases a <;> cases b <;> cases c <;> simp_all
  have hx (x : X) : (e (.inl x)).1 = (e (.inl x0)).1 :=
    bool_unique _ _ _ (hcross x y0) (hcross x0 y0)
  have hy (y : Y) : (e (.inr y)).1 = (e (.inr y0)).1 :=
    bool_unique _ _ _ (hcross x0 y).symm (hcross x0 y0).symm
  have hiX : Function.Injective (fun x : X => (e (.inl x)).2) := by
    intro x x' he
    exact Sum.inl.inj (e.injective (Prod.ext ((hx x).trans (hx x').symm) he))
  have hiY : Function.Injective (fun y : Y => (e (.inr y)).2) := by
    intro y y' he
    exact Sum.inr.inj (e.injective (Prod.ext ((hy y).trans (hy y').symm) he))
  have hsX : Function.Surjective (fun x : X => (e (.inl x)).2) := by
    intro z
    obtain ⟨u, hu⟩ := e.surjective ((e (.inl x0)).1, z)
    cases u with
    | inl x => exact ⟨x, congrArg Prod.snd hu⟩
    | inr y => exact False.elim (hcross x0 y (congrArg Prod.fst hu).symm)
  have hsY : Function.Surjective (fun y : Y => (e (.inr y)).2) := by
    intro z
    obtain ⟨u, hu⟩ := e.surjective ((e (.inr y0)).1, z)
    cases u with
    | inl x =>
      have he := congrArg (fun z : Bool × T => z.1) hu
      exact False.elim (hcross x y0 he)
    | inr y => exact ⟨y, congrArg Prod.snd hu⟩
  exact ⟨Equiv.ofBijective _ ⟨hiX, hsX⟩, Equiv.ofBijective _ ⟨hiY, hsY⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem common_tensor_chart {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y]
    (C : Matrix X Y ℝ) (hp : ∀ x y, 0 < C x y)
    (hn : ∀ u v, u ≠ v → ∀ t : ℝ, double C u ≠ t • double C v)
    (hc : NonnegativeClass (double C)) :
    ∃ d, ∃ eX : X ≃ Cube d, ∃ eY : Y ≃ Cube d,
      ∃ γ : ℝ, ∃ ρ : Fin d → ℝ,
      0 < γ ∧ (∀ r, 0 < ρ r) ∧
      ∀ x y, C x y = γ * tensor ρ (eX x) (eY y) := by
  obtain ⟨d, a, b, ρ, ha, hb, hρ, e, hm⟩ := double_bipartite_chart C hp hn hc
  let f : (X ⊕ Y) ≃ Bool × Cube d := e.trans (Equiv.prodCongr unitSides (Equiv.refl _))
  have hf (u v : X ⊕ Y) : double C u v =
      (if (f u).1 = (f v).1 then 0 else a 0 * b 0) *
        tensor ρ (f u).2 (f v).2 := by
    simpa only [f, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply] using
      (hm u v).trans (congrArg (fun z => z * tensor ρ (e u).2 (e v).2)
        (amplitude_unit a b (e u).1 (e v).1))
  have hcross (x : X) (y : Y) : (f (.inl x)).1 ≠ (f (.inr y)).1 := by
    intro he
    have h := hf (.inl x) (.inr y)
    rw [if_pos he, zero_mul] at h
    exact (ne_of_gt (hp x y)) h
  obtain ⟨eX, eY, heX, heY⟩ := split_bool_chart f hcross
  refine ⟨d, eX, eY, a 0 * b 0, ρ, mul_pos (ha 0) (hb 0), hρ, ?_⟩
  intro x y
  rw [heX, heY]
  exact (hf (.inl x) (.inr y)).trans (by rw [if_neg (hcross x y)])

end PlanarHom.RectangularBooleanCore
