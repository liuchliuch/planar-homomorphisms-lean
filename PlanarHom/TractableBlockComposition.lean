import PlanarHom.BooleanTensorFPClosure
import PlanarHom.SupportBlockTractability
import PlanarHom.RankOneEvaluationMachine

/-! NEW actual fixed finite block composition. The machine sums the literal
block values on each computed connected input component and multiplies the
answers. Empty colors, empty blocks and empty input graphs are included. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.IsingTensorTractability
export BooleanTensorFPClosure (emptyUnaries fp_product tensor_inFP product_inFP scalar_inFP color_inFP field_descent_inFP)
end PlanarHom.IsingTensorTractability

namespace PlanarHom.TractableBlockComposition
open Complexity Complexity.MixedCode RootedRestriction GraphComponentCode
variable {C B K : Type} [Fintype C] [Fintype B] [Field K] [Algebra ℚ K]
variable {dimension : ℕ}

theorem fiber_colorClosed (M : Matrix C C K) (block : C → B)
    (hzero : ∀ i j, block i ≠ block j → M i j = 0) (b : B) :
    ColorClosed M {i | block i = b} := by
  intro i hi j hij
  by_contra hn
  exact hij (hzero i j (fun he => hn (he.symm.trans hi)))

theorem partition_eq_sum_fibers (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i)
    (block : C → B) (hzero : ∀ i j, block i ≠ block j → M i j = 0) (w : C → K) :
    (g.toMultiGraph hg).partition M w =
      ∑ b : B, (g.toMultiGraph hg).partition
        (fun i j : {i // block i = b} => M i.val j.val) (fun i => w i.val) := by
  have hroot : (g.toMultiGraph hg).partition M w =
      ∑ b : B, (g.toMultiGraph hg).rootRestricted r M w {i | block i = b} := by
    unfold MultiGraph.partition MultiGraph.rootRestricted
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    simp [eq_comm]
  rw [hroot]
  apply Finset.sum_congr rfl
  intro b _
  exact rootRestricted_eq_submatrix g hg hc r M hs w _ (fiber_colorClosed M block hzero b)

theorem evaluate_eq_sum_fibers (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (support g).Connected) (hn : 0 < g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i)
    (block : C → B) (hzero : ∀ i j, block i ≠ block j → M i j = 0) (w : C → K) :
    g.evaluate hg (fun _ : Fin 1 => M) (fun u : Fin 0 => u.elim0) w =
      ∑ b : B, g.evaluate hg
        (fun _ : Fin 1 => fun i j : {i // block i = b} => M i.val j.val)
        (fun u : Fin 0 => u.elim0) (fun i => w i.val) := by
  simp_rw [evaluate_homogeneous]
  exact partition_eq_sum_fibers g hg hc ⟨0,hn⟩ M hs block hzero w

theorem fibers_inFP (basis : Module.Basis (Fin dimension) ℚ K) (block : C → B)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i)
    (hzero : ∀ i j, block i ≠ block j → M i j = 0) (w : C → K)
    (h : ∀ b : B, (evaluationProblem basis
      (fun _ : Fin 1 => fun i j : {i // block i = b} => M i.val j.val)
      (fun u : Fin 0 => u.elim0) (fun i => w i.val)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => u.elim0) w).InFP := by
  apply evaluation_inFP_of_connected basis _ _ _
  apply (restrictedEvaluation_inFP_iff basis _ _ _ (connectedCodeValid 1 0)
    (fun _ hg => hg.1.1)).mpr
  have hsum := FixedFieldPolynomialMachines.fp_sum basis
    (encoding.restrict (connectedCodeValid 1 0)) Finset.univ
    (fun (g : {g : MixedCode // connectedCodeValid 1 0 g}) (b : B) =>
      g.val.evaluate g.property.1.1
        (fun _ : Fin 1 => fun i j : {i // block i = b} => M i.val j.val)
        (fun u : Fin 0 => u.elim0) (fun i => w i.val)) (by
      intro b _
      exact (restrictedEvaluation_inFP_iff basis _ _ _ (connectedCodeValid 1 0)
        (fun _ hg => hg.1.1)).mp (connectedEvaluation_inFP_of_all basis _ _ _ (h b)))
  exact hsum.congr (fun g => (evaluate_eq_sum_fibers g.val g.property.1.1
    g.property.2.1 g.property.2.2 M hs block hzero w).symm)

end PlanarHom.TractableBlockComposition
