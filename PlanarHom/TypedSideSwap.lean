import PlanarHom.TypedContextualCoordinateTransport
import PlanarHom.TypedBipartiteContext

/-! NEW RECONSTRUCTION (2026-10-02). The concrete side swap transports the exact
ambient domains and arbitrary retained contextual labels. It does not redefine
`yFamily`, assume a chart, or assert source-family closure behind missing imports.
-/
noncomputable section
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
variable {x y s : ℕ}

/-- Pullback coordinate bijection from the swapped ambient chart to the original. -/
def swapColors (x y : ℕ) : Fin (y+x) ≃ Fin (x+y) :=
  (finSumFinEquiv : Fin y ⊕ Fin x ≃ Fin (y+x)).symm |>.trans
    ((Equiv.sumComm (Fin y) (Fin x)).trans finSumFinEquiv)

def swapDomains : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

@[simp] theorem swapDomains_zero : swapDomains 0 = 1 := by simp [swapDomains]
@[simp] theorem swapDomains_one : swapDomains 1 = 0 := by simp [swapDomains]

@[simp] theorem swapColors_left (i : Fin y) :
    swapColors x y (Fin.castAdd x i) = Fin.natAdd x i := by
  change swapColors x y (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inr i)
  simp [swapColors]

@[simp] theorem swapColors_right (i : Fin x) :
    swapColors x y (Fin.natAdd y i) = Fin.castAdd y i := by
  change swapColors x y (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inl i)
  simp [swapColors]

/-- The same fixed two domains, exchanged exactly, without any extra pinning. -/
theorem swapColors_domains :
    (fun d => swapColors x y ⁻¹' domains x y (swapDomains d)) = domains y x := by
  funext d
  apply Set.ext
  intro c
  fin_cases d
  · change c ∈ swapColors x y ⁻¹' domains x y (swapDomains 0) ↔ c ∈ domains y x 0
    rw [swapDomains_zero]
    change (∃ i : Fin y, Fin.natAdd x i = swapColors x y c) ↔
      ∃ i : Fin y, Fin.castAdd x i = c
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (swapColors x y).injective ((swapColors_left i).trans hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (swapColors_left i).symm⟩
  · change c ∈ swapColors x y ⁻¹' domains x y (swapDomains 1) ↔ c ∈ domains y x 1
    rw [swapDomains_one]
    change (∃ i : Fin x, Fin.castAdd y i = swapColors x y c) ↔
      ∃ i : Fin x, Fin.natAdd y i = c
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (swapColors x y).injective ((swapColors_right i).trans hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (swapColors_right i).symm⟩

theorem swapDomains_sameY : (fun a b => sameY (swapDomains a) (swapDomains b)) = sameX := by
  funext a b
  fin_cases a <;> fin_cases b <;> simp [sameX, sameY]

theorem swapDomains_sameX : (fun a b => sameX (swapDomains a) (swapDomains b)) = sameY := by
  funext a b
  fin_cases a <;> fin_cases b <;> simp [sameX, sameY]

theorem swapDomains_crossPolicy :
    (fun a b => crossPolicy (swapDomains a) (swapDomains b)) = crossPolicy := by
  funext a b
  apply propext
  exact not_congr swapDomains.injective.eq_iff

/-- Concrete same-source contextual side transport. All companion labels and
endpoint policies are carried through, including unrelated ordinary unaries. -/
theorem typed_contextual_side_swap
    (F : Fin s → Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s → Fin 2 → Fin 2 → Prop)
    (N : Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (NB : Fin 2 → Fin 2 → Prop)
    (hN : TypedContextuallyAvailable (domains x y) F FB N NB) :
    TypedContextuallyAvailable (domains y x)
      (fun l i j => F l (swapColors x y i) (swapColors x y j))
      (fun l a b => FB l (swapDomains a) (swapDomains b))
      (fun i j => N (swapColors x y i) (swapColors x y j))
      (fun a b => NB (swapDomains a) (swapDomains b)) := by
  have h := typed_contextual_coordinate_pullback (swapColors x y) swapDomains
    (domains x y) F FB N NB hN
  rw [swapColors_domains] at h
  exact h

/-- Exact contextual equivalence, ready to specialize to the recovered Y-family
once its independent gadget dependency cone can be compiled. -/
theorem typed_contextual_side_swap_iff
    (F : Fin s → Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s → Fin 2 → Fin 2 → Prop)
    (N : Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (NB : Fin 2 → Fin 2 → Prop) :
    TypedContextuallyAvailable (domains y x)
      (fun l i j => F l (swapColors x y i) (swapColors x y j))
      (fun l a b => FB l (swapDomains a) (swapDomains b))
      (fun i j => N (swapColors x y i) (swapColors x y j))
      (fun a b => NB (swapDomains a) (swapDomains b)) ↔
    TypedContextuallyAvailable (domains x y) F FB N NB := by
  have h := typed_contextual_coordinate_pullback_iff (swapColors x y) swapDomains
    (domains x y) F FB N NB
  rw [swapColors_domains] at h
  exact h

end PlanarHom.TypedBipartiteContext
