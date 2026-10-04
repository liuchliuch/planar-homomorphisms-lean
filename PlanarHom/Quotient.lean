import PlanarHom.Basic
import Mathlib.Logic.Equiv.Sum

/-!
# Summation over identical-row classes

The theorem `partition_fiberExpansion` proves the exact algebraic identity
underlying Definition 1.2 and the first conclusion of Corollary 3.8. It is not a
proof of their subsequent polynomial-time hardness reductions.
-/

open scoped BigOperators

noncomputable section
open Classical

namespace PlanarHom
namespace MultiGraph

variable {V E D R : Type*} [Fintype V] [Fintype E] [Fintype D]
variable [CommSemiring R]

/-- Separate a choice of class at every vertex from choices inside its class. -/
def assignmentFiberEquiv (F : D → Type*) :
    (V → Sigma F) ≃ Σ τ : V → D, ∀ v, F (τ v) where
  toFun σ := ⟨fun v => (σ v).1, fun v => (σ v).2⟩
  invFun p v := ⟨p.1 v, p.2 v⟩
  left_inv σ := by rfl
  right_inv p := by cases p; rfl

/-- Replacing every color by a finite fiber of identical colors amounts to
summing the vertex weights in that fiber. Handles loops and empty graphs. -/
theorem partition_fiberExpansion (G : MultiGraph V E) (F : D → Type*)
    [∀ d, Fintype (F d)] (M : Matrix D D R) (w : Sigma F → R) :
    G.partition (fun i j : Sigma F => M i.1 j.1) w =
      G.partition M (fun d => ∑ i : F d, w ⟨d, i⟩) := by
  classical
  unfold partition
  rw [Fintype.sum_equiv (assignmentFiberEquiv (V := V) F)
    (fun σ => G.assignmentWeight (fun i j : Sigma F => M i.1 j.1) w σ)
    (fun p => (∏ v, w ⟨p.1 v, p.2 v⟩) *
      ∏ e, M (p.1 (G.src e)) (p.1 (G.dst e))) (by intro σ; rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [assignmentWeight]
  rw [← Finset.sum_mul]
  congr 1
  exact (Fintype.prod_sum (fun v (i : F (τ v)) => w ⟨τ v, i⟩)).symm

/-- A matrix pulled back along a class map has exactly the partition function
of the class matrix with fiber-summed weights. Surjectivity is unnecessary:
empty classes receive weight zero. -/
theorem partition_pullback {C : Type*} [Fintype C]
    (G : MultiGraph V E) (π : C → D) (M : Matrix D D R) (w : C → R) :
    G.partition (fun i j => M (π i) (π j)) w =
      G.partition M (fun d => ∑ i : {c // π c = d}, w i.1) := by
  classical
  let F : D → Type _ := fun d => {c // π c = d}
  let e : Sigma F ≃ C := Equiv.sigmaFiberEquiv π
  calc
    G.partition (fun i j => M (π i) (π j)) w =
        G.partition (fun i j : Sigma F => M i.1 j.1) (fun i => w (e i)) := by
      have hm : (fun i j : Sigma F => M (π (e i)) (π (e j))) =
          (fun i j : Sigma F => M i.1 j.1) := by
        funext i j
        exact congrArg₂ M i.2.property j.2.property
      rw [← hm]
      exact (G.partition_reindexColors (fun i j => M (π i) (π j)) w e).symm
    _ = G.partition M (fun d => ∑ i : {c // π c = d}, w i.1) := by
      simpa [e, Equiv.sigmaFiberEquiv] using
        (G.partition_fiberExpansion F M (fun i => w (e i)))

/-- Exact class-weight aggregation, the algebraic part of Corollary 3.8. -/
theorem partition_eq_quotient {C : Type*} [Fintype C]
    (G : MultiGraph V E) (π : C → D) (A : Matrix C C R)
    (M : Matrix D D R) (w : C → R)
    (h : ∀ i j, A i j = M (π i) (π j)) :
    G.partition A w = G.partition M (fun d => ∑ i : {c // π c = d}, w i.1) := by
  have hA : A = fun i j => M (π i) (π j) := funext (fun i => funext (h i))
  rw [hA]
  exact G.partition_pullback π M w

end MultiGraph

namespace Twins

variable {C R : Type*}

/-- Equality of actual numerical rows, rather than equality of support rows. -/
def rowSetoid (A : Matrix C C R) : Setoid C where
  r i j := ∀ k, A i k = A j k
  iseqv := ⟨fun _ _ => rfl,
    fun h k => (h k).symm,
    fun h h' k => (h k).trans (h' k)⟩

/-- The canonical actual-row quotient of a symmetric matrix. -/
def quotientMatrix (A : Matrix C C R) (hA : ∀ i j, A i j = A j i) :
    Matrix (Quotient (rowSetoid A)) (Quotient (rowSetoid A)) R :=
  fun x y => Quotient.liftOn₂ x y A (by
    intro a b c d hac hbd
    exact (hac b).trans ((hA c b).trans ((hbd c).trans (hA d c))))

@[simp] theorem quotientMatrix_mk (A : Matrix C C R) (hA : ∀ i j, A i j = A j i)
    (i j : C) :
    quotientMatrix A hA (Quotient.mk _ i) (Quotient.mk _ j) = A i j := rfl

/-- Symmetry is retained by the actual-row quotient. -/
theorem quotientMatrix_symmetric (A : Matrix C C R) (hA : ∀ i j, A i j = A j i) :
    ∀ x y, quotientMatrix A hA x y = quotientMatrix A hA y x := by
  intro x y
  induction x using Quotient.inductionOn with
  | h i =>
    induction y using Quotient.inductionOn with
    | h j => exact hA i j

/-- The canonical quotient has no remaining pair of identical rows. -/
theorem quotientMatrix_rows_injective (A : Matrix C C R) (hA : ∀ i j, A i j = A j i) :
    Function.Injective (fun x => quotientMatrix A hA x) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h i =>
    induction y using Quotient.inductionOn with
    | h j =>
      apply Quotient.sound
      intro k
      exact congrFun h (Quotient.mk _ k)

variable [Fintype C] [CommSemiring R]

/-- The sum of original vertex weights in one actual-row class. -/
def quotientWeight (A : Matrix C C R) (w : C → R) (x : Quotient (rowSetoid A)) : R :=
  ∑ i : {c // Quotient.mk (rowSetoid A) c = x}, w i.1

set_option maxHeartbeats 800000 in
/-- Equation (1.5), including loops, isolated vertices, and the empty input.
This is the exact partition identity in Corollary 3.8; it does not assert its
additional computational reductions. -/
theorem partition_canonicalQuotient {V E : Type*} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (A : Matrix C C R) (w : C → R)
    (hA : ∀ i j, A i j = A j i) :
    G.partition A w = G.partition (quotientMatrix A hA) (quotientWeight A w) := by
  have h := G.partition_eq_quotient (Quotient.mk (rowSetoid A)) A
    (quotientMatrix A hA) w (fun _ _ => rfl)
  refine h.trans ?_
  apply congrArg (G.partition (quotientMatrix A hA))
  funext d
  unfold quotientWeight
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    rfl


end Twins
end PlanarHom
