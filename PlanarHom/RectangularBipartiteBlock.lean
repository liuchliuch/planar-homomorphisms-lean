import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Literal finite bipartite block — NEW mathematical reconstruction

The paper defines A_V = (0 V; Vᵀ 0) on printed pages 58–59, with the
two parts disjoint labelled copies of [p] and [s]. The surviving consumers
use the first p and last s finite indices, exactly the standard
`finSumFinEquiv` chart.

This module restores only that literal mathematical definition and its
entry/symmetry facts under the consumer's namespace. It does not implement
or replace the missing source-normalization simulation algorithm.
-/

namespace PlanarHom.RectangularSourceNormSimulation

variable {p s : ℕ} {R : Type*} [Zero R]

def block (C : Matrix (Fin p) (Fin s) R) :
    Matrix (Fin (p + s)) (Fin (p + s)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C C.transpose 0)

@[simp] theorem block_left_left (C : Matrix (Fin p) (Fin s) R) (i j : Fin p) :
    block C (Fin.castAdd s i) (Fin.castAdd s j) = 0 := by
  simp [block]

@[simp] theorem block_left_right (C : Matrix (Fin p) (Fin s) R)
    (i : Fin p) (j : Fin s) :
    block C (Fin.castAdd s i) (Fin.natAdd p j) = C i j := by
  simp [block]

@[simp] theorem block_right_left (C : Matrix (Fin p) (Fin s) R)
    (i : Fin s) (j : Fin p) :
    block C (Fin.natAdd p i) (Fin.castAdd s j) = C j i := by
  simp [block]

@[simp] theorem block_right_right (C : Matrix (Fin p) (Fin s) R) (i j : Fin s) :
    block C (Fin.natAdd p i) (Fin.natAdd p j) = 0 := by
  simp [block]

theorem block_symm (C : Matrix (Fin p) (Fin s) R) :
    ∀ i j, block C i j = block C j i := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

end PlanarHom.RectangularSourceNormSimulation
