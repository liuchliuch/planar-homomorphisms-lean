import PlanarHom.BipartiteFullTwinFinite
import Mathlib.Tactic.NormNum

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.BipartiteFullTwins.AdapterV2Regressions

open RectangularTwinQuotient
open RectangularSourceNormSimulation (block)

/-- Empty sides are not silently excluded from the reconstructed bridge. -/
def regression_1 :
    Quotient (Twins.rowSetoid (block (fun (_ : Fin 0) (_ : Fin 0) => (1 : ℝ)))) ≃
      Rows (fun (_ : Fin 0) (_ : Fin 0) => (1 : ℝ)) ⊕
      Columns (fun (_ : Fin 0) (_ : Fin 0) => (1 : ℝ)) :=
  finSideEquiv _ (by intros; norm_num)

/-- A single empty side is also allowed, without a hidden nonempty hypothesis. -/
def regression_2 :
    Quotient (Twins.rowSetoid (block (fun (_ : Fin 0) (_ : Fin 3) => (1 : ℝ)))) ≃
      Rows (fun (_ : Fin 0) (_ : Fin 3) => (1 : ℝ)) ⊕
      Columns (fun (_ : Fin 0) (_ : Fin 3) => (1 : ℝ)) :=
  finSideEquiv _ (by intros; norm_num)

def unequal : Matrix (Fin 2) (Fin 3) ℝ := fun _ _ => 1

theorem unequal_positive : ∀ i j, 0 < unequal i j := by
  intros
  norm_num [unequal]

/-- Even when all original rows agree on each side, the two sides remain
distinct real numerical-row classes. -/
theorem regression_3 :
    (Quotient.mk (Twins.rowSetoid (block unequal)) (Fin.castAdd 3 0)) ≠
      Quotient.mk _ (Fin.natAdd 2 0) := by
  intro h
  have he := congrArg (finSideEquiv unequal unequal_positive) h
  rw [finSideEquiv_mk, finSideEquiv_mk] at he
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    sideClass, Sum.map_inl, Sum.map_inr, Sum.inl_ne_inr] at he

/-- Arbitrary independent side weights survive at the zeroth moment, including
zero and signed weights. The theorem imposes no positivity on them. -/
theorem regression_4 (μ : Fin 2 → ℝ) (ν : Fin 3 → ℝ)
    (α : Fin 2 → ℝ) (β : Fin 3 → ℝ)
    (q : Quotient (Twins.rowSetoid (block unequal))) :
    Twins.quotientWeight (block unequal) (Fin.addCases μ ν) q =
      sideWeight unequal μ ν (finSideEquiv unequal unequal_positive q) := by
  simpa [sideWeight] using
    quotientMoment_finSideEquiv unequal unequal_positive μ α ν β 0 q

/-- Unequal side sizes and weights give genuinely unequal total masses: 4. -/
theorem regression_5 :
    Twins.quotientWeight (block unequal)
      (Fin.addCases (fun _ : Fin 2 => (2 : ℝ)) (fun _ : Fin 3 => (3 : ℝ)))
      (Quotient.mk _ (Fin.castAdd 3 0)) = 4 := by
  rw [quotientWeight_finSideEquiv unequal unequal_positive, finSideEquiv_mk]
  simp only [finSumFinEquiv_symm_apply_castAdd, sideClass, Sum.map_inl,
    sideWeight, Sum.elim_inl]
  rw [fiber_sum_eq_ite (Quotient.mk (rowSetoid unequal))
    (fun _ : Fin 2 => (2 : ℝ)) (Quotient.mk _ 0)]
  have h (i : Fin 2) :
      Quotient.mk (rowSetoid unequal) i = Quotient.mk (rowSetoid unequal) 0 :=
    Quotient.sound rfl
  norm_num [h]

/-- The same real quotient and same weights give mass 9 on the other side. -/
theorem regression_6 :
    Twins.quotientWeight (block unequal)
      (Fin.addCases (fun _ : Fin 2 => (2 : ℝ)) (fun _ : Fin 3 => (3 : ℝ)))
      (Quotient.mk _ (Fin.natAdd 2 0)) = 9 := by
  rw [quotientWeight_finSideEquiv unequal unequal_positive, finSideEquiv_mk]
  simp only [finSumFinEquiv_symm_apply_natAdd, sideClass, Sum.map_inr,
    sideWeight, Sum.elim_inr]
  rw [fiber_sum_eq_ite (Quotient.mk (columnSetoid unequal))
    (fun _ : Fin 3 => (3 : ℝ)) (Quotient.mk _ 0)]
  have h (i : Fin 3) :
      Quotient.mk (columnSetoid unequal) i = Quotient.mk (columnSetoid unequal) 0 :=
    Quotient.sound rfl
  norm_num [h]

def numerical : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = 0 ∧ j = 0 then 2 else 1

/-- Full support does not collapse numerically distinct rows. -/
theorem regression_7 :
    (Quotient.mk (rowSetoid numerical) 0) ≠ Quotient.mk _ 1 := by
  intro h
  have he := congrFun (Quotient.exact h) 0
  norm_num [rowSetoid, numerical] at he

/-- All moment orders use one fixed quotient equivalence, with no comparison
between the cardinalities or masses of the original sides. -/
theorem regression_8 (C : Matrix (Fin 2) (Fin 3) ℝ) (hC : ∀ i j, 0 < C i j)
    (μ α : Fin 2 → ℝ) (ν β : Fin 3 → ℝ) (m : ℕ)
    (q : Quotient (Twins.rowSetoid (block C))) :
    Twins.quotientWeight (block C)
      (fun i => Fin.addCases μ ν i * (Fin.addCases α β i) ^ (2 * m)) q =
      sideWeight C (fun i => μ i * (α i) ^ (2 * m))
        (fun j => ν j * (β j) ^ (2 * m)) (finSideEquiv C hC q) :=
  quotientMoment_finSideEquiv C hC μ α ν β m q

end PlanarHom.BipartiteFullTwins.AdapterV2Regressions
