import PlanarHom.RectangularTwinQuotient
import PlanarHom.Quotient
import Mathlib.Data.Matrix.Block

/-! The full numerical-row quotient of a strictly positive bipartite double
is exactly the sum of the rectangular row and column quotients. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BipartiteFullTwins
open RectangularTwinQuotient
variable {X Y : Type}

def double (C : Matrix X Y ℝ) : Matrix (X⊕Y) (X⊕Y) ℝ :=
  Matrix.fromBlocks 0 C C.transpose 0

theorem double_symmetric (C : Matrix X Y ℝ) : ∀ i j,double C i j=double C j i := by
  intro i j
  cases i <;> cases j <;> rfl

def sideClass (C : Matrix X Y ℝ) : X⊕Y → Rows C⊕Columns C :=
  Sum.map (Quotient.mk (rowSetoid C)) (Quotient.mk (columnSetoid C))


theorem row_relation_iff (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) (u v : X⊕Y) :
    Twins.rowSetoid (double C) u v ↔ sideClass C u=sideClass C v := by
  cases u with
  | inl x =>
    cases v with
    | inl x' =>
      constructor
      · intro h
        apply congrArg Sum.inl
        apply Quotient.sound
        funext y
        exact h (.inr y)
      · intro h
        have hr := Quotient.exact (Sum.inl.inj h)
        intro z
        cases z with
        | inl z => rfl
        | inr y => exact congrFun hr y
    | inr y =>
      constructor
      · intro h
        have hz := h (.inr y)
        have hp := hC x y
        change C x y=0 at hz
        exact (ne_of_gt hp hz).elim
      · intro h
        exact Sum.noConfusion h
  | inr y =>
    cases v with
    | inl x =>
      constructor
      · intro h
        have hz := h (.inl x)
        have hp := hC x y
        change C x y=0 at hz
        exact (ne_of_gt hp hz).elim
      · intro h
        exact Sum.noConfusion h
    | inr y' =>
      constructor
      · intro h
        apply congrArg Sum.inr
        apply Quotient.sound
        funext x
        exact h (.inl x)
      · intro h
        have hr := Quotient.exact (Sum.inr.inj h)
        intro z
        cases z with
        | inl x => exact congrFun hr x
        | inr z => rfl

def sideMap (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) :
    Quotient (Twins.rowSetoid (double C)) → Rows C⊕Columns C :=
  Quotient.lift (sideClass C) (fun u v h => (row_relation_iff C hC u v).mp h)

theorem sideMap_bijective (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) :
    Function.Bijective (sideMap C hC) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h u =>
      induction b using Quotient.inductionOn with
      | h v =>
        intro h
        exact Quotient.sound ((row_relation_iff C hC u v).mpr h)
  · intro z
    cases z with
    | inl r =>
      refine ⟨Quotient.mk _ (Sum.inl r.out),?_⟩
      exact congrArg Sum.inl (Quotient.out_eq r)
    | inr s =>
      refine ⟨Quotient.mk _ (Sum.inr s.out),?_⟩
      exact congrArg Sum.inr (Quotient.out_eq s)

def sideEquiv (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) :
    Quotient (Twins.rowSetoid (double C)) ≃ Rows C⊕Columns C :=
  Equiv.ofBijective (sideMap C hC) (sideMap_bijective C hC)

@[simp] theorem sideEquiv_mk (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) (z : X⊕Y) :
    sideEquiv C hC (Quotient.mk _ z)=sideClass C z := rfl

theorem quotientMatrix_sideEquiv (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y)
    (a b : Quotient (Twins.rowSetoid (double C))) :
    Twins.quotientMatrix (double C) (double_symmetric C) a b =
      double (core C) (sideEquiv C hC a) (sideEquiv C hC b) := by
  induction a using Quotient.inductionOn with
  | h u =>
    induction b using Quotient.inductionOn with
    | h v =>
      rw [sideEquiv_mk,sideEquiv_mk]
      cases u <;> cases v <;>
        simp [double,sideClass,core_entry]

variable [Fintype X] [Fintype Y]

theorem fiber_sum_eq_ite {A Q : Type*} [Fintype A] (f : A → Q) (w : A → ℝ) (q : Q)
    [Fintype {a // f a=q}] :
    (∑ a : {a // f a=q}, w a.val) = ∑ a, if f a=q then w a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun a => f a=q)) (by simp) w).symm

def sideWeight (C : Matrix X Y ℝ) (μ : X → ℝ) (ν : Y → ℝ) : Rows C⊕Columns C → ℝ :=
  Sum.elim (fun r => ∑ x : {x // Quotient.mk (rowSetoid C) x=r}, μ x.val)
    (fun s => ∑ y : {y // Quotient.mk (columnSetoid C) y=s}, ν y.val)

/-- The full quotient's masses are the literal sums on their original sides.
No equality between the two side masses or cardinalities is imposed. -/
theorem quotientWeight_sideEquiv (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y)
    (μ : X → ℝ) (ν : Y → ℝ) (a : Quotient (Twins.rowSetoid (double C))) :
    Twins.quotientWeight (double C) (Sum.elim μ ν) a =
      sideWeight C μ ν (sideEquiv C hC a) := by
  have he (z : X⊕Y) : Quotient.mk (Twins.rowSetoid (double C)) z=a ↔
      sideClass C z=sideEquiv C hC a := (sideEquiv C hC).injective.eq_iff.symm
  unfold Twins.quotientWeight
  rw [fiber_sum_eq_ite (Quotient.mk (Twins.rowSetoid (double C))) (Sum.elim μ ν) a,
    Fintype.sum_sum_type]
  simp_rw [he]
  cases hz : sideEquiv C hC a <;>
    simp only [sideWeight, sideClass, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inr_ne_inl, Sum.inl_ne_inr, if_false,
      Finset.sum_const_zero, zero_add, add_zero, fiber_sum_eq_ite]
  all_goals
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl

end PlanarHom.BipartiteFullTwins
