import PlanarHom.CommonWeightedAmplitudeCoordinates
import Mathlib.Logic.Equiv.Fintype

/-! NEW: equal finite power moments identify the actual multiplicity of each
value, hence give a value-preserving bijection. Repeated values and empty types
are retained; no amplitude injectivity is assumed. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.FiniteMomentFiberEquivalence

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem exists_value_preserving_equiv (f : X → ℝ) (g : Y → ℝ)
    (hmom : ∀ m : ℕ, (∑ x, f x ^ m) = ∑ y, g y ^ m) :
    ∃ e : X ≃ Y, ∀ x, g (e x) = f x := by
  let support : Finset ℝ := Finset.univ.image f ∪ Finset.univ.image g
  let I := {r : ℝ // r ∈ support}
  let a : X → I := fun x => ⟨f x, Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)⟩
  let b : Y → I := fun y => ⟨g y, Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)⟩
  let cx : I → ℝ := fun r => ∑ x : X, if a x = r then 1 else 0
  let cy : I → ℝ := fun r => ∑ y : Y, if b y = r then 1 else 0
  have hx (m : ℕ) : (∑ r : I, cx r * r.val ^ m) = ∑ x, f x ^ m := by
    simp only [cx, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single (a x)]
    · simp [a]
    · intro r _ hne
      simp [Ne.symm hne]
    · simp
  have hy (m : ℕ) : (∑ r : I, cy r * r.val ^ m) = ∑ y, g y ^ m := by
    simp only [cy, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (b y)]
    · simp [b]
    · intro r _ hne
      simp [Ne.symm hne]
    · simp
  have hc : cx = cy := by
    apply CommonWeightedAmplitudeCoordinates.finite_type_moment_unique Subtype.val_injective
    intro m
    exact (hx m).trans ((hmom m).trans (hy m).symm)
  have hcard (r : I) : Fintype.card {x // a x = r} = Fintype.card {y // b y = r} := by
    have h := congrFun hc r
    have hxcard : cx r = (Fintype.card {x // a x = r} : ℝ) := by
      simp only [cx, Fintype.card_subtype]
      exact Finset.sum_boole (fun x => a x = r) Finset.univ
    have hycard : cy r = (Fintype.card {y // b y = r} : ℝ) := by
      simp only [cy, Fintype.card_subtype]
      exact Finset.sum_boole (fun y => b y = r) Finset.univ
    rw [hxcard, hycard] at h
    exact_mod_cast h
  let E : ∀ r : I, {x // a x = r} ≃ {y // b y = r} :=
    fun r => Fintype.equivOfCardEq (hcard r)
  let e : X ≃ Y := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨e, ?_⟩
  intro x
  have h := (E (a x) ⟨x, rfl⟩).property
  exact congrArg Subtype.val h

end PlanarHom.FiniteMomentFiberEquivalence
