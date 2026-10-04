import PlanarHom.CubeGraphMetric
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! NEW reconstruction of the literal Cartesian distance-kernel identities
used to isolate clique sizes in the Section 6 common-chart argument. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace PlanarHom.HammingKernelTensor
open CartesianGeometry

/-- Extended distance in the varying-alphabet Hamming graph is its actual
number of differing coordinates, including the empty Cartesian product. -/
theorem hamming_edist {d : ℕ} (A : Fin d → Type*) (u v : ∀ r, A r) :
    (hammingGraph A).edist u v =
      ((∑ r : Fin d, if u r = v r then 0 else 1 : ℕ) : ℕ∞) := by
  classical
  induction d with
  | zero =>
    have h : u = v := Subsingleton.elim _ _
    subst v
    simp [SimpleGraph.edist_self]
  | succ d ih =>
    let e := hammingGraph_finSucc A
    rw [Boolean.graphIso_edist_eq e u v, SimpleGraph.edist_boxProd, SimpleGraph.edist_top]
    change (if u 0 = v 0 then (0 : ℕ∞) else 1) +
      (hammingGraph (fun r : Fin d => A r.succ)).edist
        (fun r => u r.succ) (fun r => v r.succ) = _
    rw [ih, Fin.sum_univ_succ, Nat.cast_add]
    by_cases h : u 0 = v 0 <;> simp [h]

theorem hamming_dist {d : ℕ} (A : Fin d → Type*) (u v : ∀ r, A r) :
    (hammingGraph A).dist u v = ∑ r : Fin d, if u r = v r then 0 else 1 := by
  classical
  unfold SimpleGraph.dist
  rw [hamming_edist]
  exact ENat.toNat_coe _

/-- The tensor is defined on literal dependent-coordinate colors. -/
def tensor {I : Type*} [Fintype I] {A : I → Type*} {R : Type*} [CommMonoid R]
    (M : ∀ r, Matrix (A r) (A r) R) : Matrix (∀ r, A r) (∀ r, A r) R :=
  fun u v => ∏ r, M r (u r) (v r)

/-- Literal finite-sum Fubini gives multiplication of varying-size tensors. -/
theorem tensor_mul {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ r, Fintype (A r)] {R : Type*} [CommSemiring R]
    (M N : ∀ r, Matrix (A r) (A r) R) :
    tensor M * tensor N = tensor (fun r => M r * N r) := by
  ext u v
  simp only [Matrix.mul_apply, tensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun r z => M r (u r) z * N r z (v r))).symm

/-- A clique kernel has diagonal one and off-diagonal the parameter. -/
def cliqueKernel {A : Type*} (t : ℝ) : Matrix A A ℝ :=
  fun i j => if i = j then 1 else t

theorem distanceKernel_eq_tensor {d : ℕ} (A : Fin d → Type*) (t : ℝ) :
    EntropyCompletion.distanceKernel (hammingGraph A) t =
      tensor (fun r => (cliqueKernel t : Matrix (A r) (A r) ℝ)) := by
  classical
  ext u v
  change t ^ (hammingGraph A).dist u v = ∏ r, if u r = v r then 1 else t
  rw [hamming_dist, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : u r = v r <;> simp [h]

end PlanarHom.HammingKernelTensor
