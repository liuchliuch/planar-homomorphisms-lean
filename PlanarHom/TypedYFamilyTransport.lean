import PlanarHom.TypedSideSwap
import PlanarHom.RectangularBipartiteBlock

/-! NEW reconstruction. Literal Y-family and same-source side transport.
The recovered definition of `yFamily` is retained exactly. The absent physical
forms used by its historical import are replaced here only by explicit block
coordinates; no gadget, source reduction, or common chart is assumed. -/
noncomputable section
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral
variable {x y s : ℕ}

def crossFin {R : Type} [Field R] (B : Matrix (Fin x) (Fin y) R) : Matrix (Fin (x+y)) (Fin (x+y)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B B.transpose 0)

def onYFin {R : Type} [Field R] (K : Matrix (Fin y) (Fin y) R) : Matrix (Fin (x+y)) (Fin (x+y)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 K)

/-- Authentic recovered membership, preserving arbitrary retained companions. -/
def yFamily (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : Set (Matrix (Fin y) (Fin y) ℝ) :=
  {N | N.IsHermitian ∧ TypedContextuallyAvailable (domains x y) F FB (onYFin N) sameY}

@[simp] theorem onYFin_right (N : Matrix (Fin y) (Fin y) ℝ) (i j : Fin y) :
    onYFin (x:=x) N (Fin.natAdd x i) (Fin.natAdd x j)=N i j := by
  simp [onYFin]

theorem swap_onYFin (N : Matrix (Fin y) (Fin y) ℝ) :
    (fun i j => onYFin (x:=x) N (swapColors x y i) (swapColors x y j)) =
      zeroExtendFin (y:=x) N := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [swapColors_left, swapColors_right, onYFin, zeroExtendFin, zeroExtend]

theorem swap_zeroExtendFin (N : Matrix (Fin x) (Fin x) ℝ) :
    (fun i j => zeroExtendFin (y:=y) N (swapColors x y i) (swapColors x y j)) =
      onYFin (x:=y) N := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [swapColors_left, swapColors_right, onYFin, zeroExtendFin, zeroExtend]

theorem swap_crossFin (B : Matrix (Fin x) (Fin y) ℝ) :
    (fun i j => crossFin B (swapColors x y i) (swapColors x y j)) =
      crossFin B.transpose := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [swapColors_left, swapColors_right, crossFin]

/-- Equality of the actual contextual families; inherited reductions carry all
retained matrices, unaries, policies, and original field representations. -/
theorem yFamily_eq_swapped_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop) :
    yFamily F FB = xFamily
      (fun l i j => F l (swapColors x y i) (swapColors x y j))
      (fun l a b => FB l (swapDomains a) (swapDomains b)) := by
  apply Set.ext
  intro N
  change (N.IsHermitian ∧ _) ↔ (N.IsHermitian ∧ _)
  apply and_congr_right
  intro _
  have h := typed_contextual_side_swap_iff F FB (onYFin N) sameY
  rw [swap_onYFin, swapDomains_sameY] at h
  exact h.symm

theorem xFamily_eq_swapped_yFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop) :
    xFamily F FB = yFamily
      (fun l i j => F l (swapColors x y i) (swapColors x y j))
      (fun l a b => FB l (swapDomains a) (swapDomains b)) := by
  apply Set.ext
  intro N
  change (N.IsHermitian ∧ _) ↔ (N.IsHermitian ∧ _)
  apply and_congr_right
  intro _
  have h := typed_contextual_side_swap_iff F FB (zeroExtendFin N) sameX
  rw [swap_zeroExtendFin, swapDomains_sameX] at h
  exact h.symm

theorem yFamily_algebraic (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (N : Matrix (Fin y) (Fin y) ℝ)
    (hN : N∈yFamily F FB) : ∀ i j, IsAlgebraic ℚ (N i j) := by
  intro i j
  simpa only [onYFin_right] using hN.2.algebraic (Fin.natAdd x i) (Fin.natAdd x j)

end PlanarHom.TypedBipartiteContext
