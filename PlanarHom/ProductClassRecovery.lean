import PlanarHom.LagrangeRecovery

/-! Zero-product exclusion and exact recovery from nonzero product classes. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.LagrangeRecovery
variable {A K : Type} [Fintype A] [Field K] {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- Finite sums can discard exactly those assignments whose contribution is zero. -/
theorem sum_eq_nonzero_subtype (source f : A → K)
    (hz : ∀ a, source a = 0 → f a = 0) :
    (∑ a, f a) = ∑ a : {a // source a ≠ 0}, f a.val := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun a => source a ≠ 0) f
  have hzero : (∑ a : {a // ¬source a ≠ 0}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hz a.val (not_ne_iff.mp a.property)
  simpa only [hzero, add_zero] using hs.symm

/-- Genuine positive-power queries and zero-preserving target products are recovered
from any verified enumeration of distinct nonzero product classes. -/
theorem evaluateReplacement_nonzero_classes (source target rest : A → K)
    (hz : ∀ a, source a = 0 → target a = 0)
    (classOf : {a // source a ≠ 0} → Fin n) (μ η : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0)
    (hsource : ∀ a, μ (classOf a) = source a.val)
    (htarget : ∀ a, η (classOf a) = target a.val) :
    evaluateReplacement μ η (fun h => ∑ a, rest a * source a ^ (h.val + 1)) =
      ∑ a, rest a * target a := by
  have hquery (h : Fin n) : (∑ a, rest a * source a ^ (h.val + 1)) =
      ∑ a : {a // source a ≠ 0}, rest a.val * μ (classOf a) ^ (h.val + 1) := by
    rw [sum_eq_nonzero_subtype source _ (fun a ha => by simp [ha])]
    simp only [hsource]
  have hq := funext hquery
  rw [hq, evaluateReplacement_grouped_queries classOf (fun a => rest a.val) μ η hμ hzero]
  rw [sum_eq_nonzero_subtype source _ (fun a ha => by simp [hz a ha])]
  apply Finset.sum_congr rfl
  intro a _
  rw [htarget, mul_comm]

end PlanarHom.LagrangeRecovery
