import PlanarHom.MixedProductZeros
import PlanarHom.ProductClassRecovery

/-!
# Joint binary and unary replacement: exact query/recovery identities

The input class data are the precise invariants the implemented enumeration and
collision-merging algorithm must establish. All unchanged signed factors,
background weights, source-zero assignments and occurrence multiplicities are
handled by the actual mixed partition semantics.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open LagrangeRecovery
variable {C K : Type} [Fintype C] [Field K] {binaryTypes unaryTypes n : ℕ}
attribute [local instance] Classical.propDecidable

/-- Exact binary-label replacement by the actual positive parallel queries and
coefficient-dot-query Lagrange recovery. No zero source assignment is retained. -/
theorem binary_replacement_recovered
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) (selected : ℕ)
    (M M' : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K)
    (hunchanged : ∀ l, l.val ≠ selected → M' l = M l)
    (hzero : ∀ l i j, l.val = selected → M l i j = 0 → M' l i j = 0)
    (classOf : {σ : Fin g.vertices → C // selectedBinaryProduct g selected M σ ≠ 0} → Fin n)
    (μ η : Fin n → K) (hμ : Function.Injective μ) (hμzero : ∀ j, μ j ≠ 0)
    (hsource : ∀ σ, μ (classOf σ) = selectedBinaryProduct g selected M σ.val)
    (htarget : ∀ σ, η (classOf σ) = selectedBinaryProduct g selected M' σ.val) :
    evaluateReplacement μ η (fun h : Fin n =>
      (g.parallelLabel selected (h.val + 1)).evaluate
        (parallelLabel_valid selected (h.val + 1) binaryTypes unaryTypes g hg) M U w) =
      g.evaluate hg M' U w := by
  simp_rw [evaluate_parallelLabel_eq_power_sum g hg selected _ M U w]
  have h := evaluateReplacement_nonzero_classes
    (selectedBinaryProduct g selected M) (selectedBinaryProduct g selected M')
    (binaryRemainder g selected M U w)
    (fun σ hz => selectedBinaryProduct_zero_of_zero g selected M M' hzero σ hz)
    classOf μ η hμ hμzero hsource htarget
  rw [h, evaluate_eq_binary_product_sum g hg selected M' U w]
  apply Finset.sum_congr rfl
  intro σ _
  rw [binaryRemainder_congr g selected M M' U w hunchanged]

/-- Exact unary-label replacement; the corresponding query graphs are ordinary
planar whenever the original graph is, with no geometric ribbon premise. -/
theorem unary_replacement_recovered
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) (selected : ℕ)
    (M : Fin binaryTypes → Matrix C C K) (U U' : Fin unaryTypes → C → K) (w : C → K)
    (hunchanged : ∀ l, l.val ≠ selected → U' l = U l)
    (hzero : ∀ l i, l.val = selected → U l i = 0 → U' l i = 0)
    (classOf : {σ : Fin g.vertices → C // selectedUnaryProduct g selected U σ ≠ 0} → Fin n)
    (μ η : Fin n → K) (hμ : Function.Injective μ) (hμzero : ∀ j, μ j ≠ 0)
    (hsource : ∀ σ, μ (classOf σ) = selectedUnaryProduct g selected U σ.val)
    (htarget : ∀ σ, η (classOf σ) = selectedUnaryProduct g selected U' σ.val) :
    evaluateReplacement μ η (fun h : Fin n =>
      (g.parallelUnaryLabel selected (h.val + 1)).evaluate
        (parallelUnaryLabel_valid selected (h.val + 1) g hg) M U w) =
      g.evaluate hg M U' w := by
  simp_rw [evaluate_parallelUnaryLabel_eq_power_sum g hg selected _ M U w]
  have h := evaluateReplacement_nonzero_classes
    (selectedUnaryProduct g selected U) (selectedUnaryProduct g selected U')
    (unaryRemainder g selected M U w)
    (fun σ hz => selectedUnaryProduct_zero_of_zero g selected U U' hzero σ hz)
    classOf μ η hμ hμzero hsource htarget
  rw [h, evaluate_eq_unary_product_sum g hg selected M U' w]
  apply Finset.sum_congr rfl
  intro σ _
  rw [unaryRemainder_congr g selected M U U' w hunchanged]

end PlanarHom.Complexity.MixedCode
