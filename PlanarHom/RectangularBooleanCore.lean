import PlanarHom.RectangularBooleanSides

/-! NEW rectangular structural extraction for Appendix A.12. The two original
finite sides are independently identified with one common Boolean cube.
Strict positivity and absence of proportional rows/columns suffice; no rank
or chart certificate is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularBooleanCore
open Structures Boolean BipartiteFullTwins

theorem tensor_rows_eq_of_parameter_one {d : ℕ} (ρ : Fin d → ℝ) (r : Fin d)
    (hr : ρ r = 1) (z : Cube d) :
    tensor ρ (fun _ => false) z = tensor ρ (unitBit r) z := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = r
  · subst i
    simp [W, unitBit, hr]
  · simp [unitBit, hi]

theorem parameters_ne_one {X Y : Type} {d : ℕ}
    (C : Matrix X Y ℝ)
    (hrows : ∀ x x', x ≠ x' → ∀ t : ℝ, C x ≠ t • C x')
    (eX : X ≃ Cube d) (eY : Y ≃ Cube d) (γ : ℝ) (ρ : Fin d → ℝ)
    (hm : ∀ x y, C x y = γ * tensor ρ (eX x) (eY y)) :
    ∀ r, ρ r ≠ 1 := by
  intro r hr
  let x := eX.symm (fun _ => false)
  let x' := eX.symm (unitBit r)
  have hne : x ≠ x' := by
    intro he
    have h := congrFun (eX.symm.injective he) r
    simp [unitBit] at h
  apply hrows x x' hne 1
  rw [one_smul]
  funext y
  simp only [hm, x, x', Equiv.apply_symm_apply]
  rw [tensor_rows_eq_of_parameter_one ρ r hr]

/-- A strictly positive rectangular matrix with no distinct proportional
rows or columns has a common nondegenerate scaled Boolean tensor chart as
soon as its literal bipartite double belongs to the nonnegative class. -/
theorem tensor_core_of_nonnegativeClass {X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (C : Matrix X Y ℝ) (hp : ∀ x y, 0 < C x y)
    (hrows : ∀ x x', x ≠ x' → ∀ t : ℝ, C x ≠ t • C x')
    (hcols : ∀ y y', y ≠ y' → ∀ t : ℝ, C.transpose y ≠ t • C.transpose y')
    (hc : NonnegativeClass (double C)) :
    ∃ d, ∃ eX : X ≃ Cube d, ∃ eY : Y ≃ Cube d,
      ∃ γ : ℝ, ∃ ρ : Fin d → ℝ,
      0 < γ ∧ (∀ r, 0 < ρ r ∧ ρ r ≠ 1) ∧
      ∀ x y, C x y = γ * tensor ρ (eX x) (eY y) := by
  obtain ⟨d, eX, eY, γ, ρ, hγ, hρ, hm⟩ :=
    common_tensor_chart C hp (double_nonproportional C hp hrows hcols) hc
  exact ⟨d, eX, eY, γ, ρ, hγ,
    fun r => ⟨hρ r, parameters_ne_one C hrows eX eY γ ρ hm r⟩, hm⟩

end PlanarHom.RectangularBooleanCore
