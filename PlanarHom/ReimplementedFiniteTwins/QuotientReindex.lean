import PlanarHom.Quotient

/-!
New reconstruction, not recovered historical source.

Numerical-row quotients, their matrices, and their literal fiber weights
commute with a bijective relabeling of the original colors. This module
requires no normalization, positivity, or source-availability assumptions.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Twins.ReconstructedReindex

variable {C D R : Type*}

def matrix (A : Matrix C C R) (e : D ≃ C) : Matrix D D R :=
  fun i j => A (e i) (e j)

theorem row_relation_iff (A : Matrix C C R) (e : D ≃ C) (i j : D) :
    rowSetoid (matrix A e) i j ↔ rowSetoid A (e i) (e j) := by
  constructor
  · intro h k
    simpa only [matrix, Equiv.apply_symm_apply] using h (e.symm k)
  · intro h k
    exact h (e k)

def quotientEquiv (A : Matrix C C R) (e : D ≃ C) :
    Quotient (rowSetoid (matrix A e)) ≃ Quotient (rowSetoid A) :=
  Quotient.congr e (row_relation_iff A e)

@[simp] theorem quotientEquiv_mk (A : Matrix C C R) (e : D ≃ C) (i : D) :
    quotientEquiv A e (Quotient.mk _ i) = Quotient.mk _ (e i) := rfl

theorem symmetric (A : Matrix C C R) (e : D ≃ C)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, matrix A e i j = matrix A e j i :=
  fun i j => hA (e i) (e j)

theorem quotientMatrix_transport (A : Matrix C C R) (e : D ≃ C)
    (hA : ∀ i j, A i j = A j i)
    (a b : Quotient (rowSetoid (matrix A e))) :
    quotientMatrix (matrix A e) (symmetric A e hA) a b =
      quotientMatrix A hA (quotientEquiv A e a) (quotientEquiv A e b) := by
  induction a using Quotient.inductionOn with
  | h i =>
    induction b using Quotient.inductionOn with
    | h j => rfl

def fiberEquiv (A : Matrix C C R) (e : D ≃ C)
    (a : Quotient (rowSetoid (matrix A e))) :
    {i // Quotient.mk (rowSetoid (matrix A e)) i = a} ≃
      {j // Quotient.mk (rowSetoid A) j = quotientEquiv A e a} where
  toFun i := ⟨e i.val, by
    exact congrArg (quotientEquiv A e) i.property⟩
  invFun j := ⟨e.symm j.val, by
    apply (quotientEquiv A e).injective
    simpa only [quotientEquiv_mk, Equiv.apply_symm_apply] using j.property⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

variable [Fintype C] [Fintype D] [CommSemiring R]

theorem quotientWeight_transport (A : Matrix C C R) (e : D ≃ C)
    (w : C → R) (a : Quotient (rowSetoid (matrix A e))) :
    quotientWeight (matrix A e) (fun i => w (e i)) a =
      quotientWeight A w (quotientEquiv A e a) := by
  unfold quotientWeight
  exact Fintype.sum_equiv (fiberEquiv A e a) _ _ (fun _ => rfl)

end PlanarHom.Twins.ReconstructedReindex
