import PlanarHom.SupportBlockSemantics
import PlanarHom.GraphComponentTractability
import PlanarHom.FixedFieldPolynomialMachines

/-! The final tractability implication of source Lemma 3.5. Each block hypothesis
is exact promised TM2 computation of its actual numerical support-component
submatrix in the original fixed number-field basis. The proof compiles the
finite block calls and field additions, computes the input's real components,
and multiplies the answers, with every successful raw encoding covered. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.RootedRestriction
open Complexity Complexity.MixedCode GraphComponentCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension : ℕ}

/-- The fixed finite sum is compiled by genuine number-field addition machines.
There is one exact call per actual color support component; their number depends
only on the fixed source matrix, never on the input graph. -/
theorem fp_connectedSupportBlockSum (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K)
    (h : ∀ c : (colorSupport M hs).ConnectedComponent,
      (connectedEvaluationProblem basis (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val)).InFP) :
    FP (encoding.restrict (connectedCodeValid 1 0)) (numberFieldEncoding basis)
      (fun g : {g : MixedCode // connectedCodeValid 1 0 g} =>
        ∑ c : (colorSupport M hs).ConnectedComponent,
          g.val.evaluate g.property.1.1 (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
            (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val)) := by
  apply FixedFieldPolynomialMachines.fp_sum basis _ Finset.univ
  intro c _
  exact (restrictedEvaluation_inFP_iff basis _ _ _ (connectedCodeValid 1 0)
    (fun _ hg => hg.1.1)).mp (h c)

/-- Connected full-source evaluation is in promised FP whenever each literal
support-component problem is in promised FP on connected planar inputs. -/
theorem connected_supportBlocks_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K)
    (h : ∀ c : (colorSupport M hs).ConnectedComponent,
      (connectedEvaluationProblem basis (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val)).InFP) :
    (connectedEvaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).InFP := by
  apply (restrictedEvaluation_inFP_iff basis _ _ _ (connectedCodeValid 1 0)
    (fun _ hg => hg.1.1)).mpr
  exact (fp_connectedSupportBlockSum basis M hs w h).congr (fun g =>
    (evaluate_eq_sum_supportBlocks g.val g.property.1.1 g.property.2.1 g.property.2.2 M hs w).symm)

/-- The strongest form needs block algorithms only on connected inputs. Every
input component is actually computed, every block answer uses the same original
basis, and empty input returns the empty product one. -/
theorem supportBlocks_inFP_of_connected (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K)
    (h : ∀ c : (colorSupport M hs).ConnectedComponent,
      (connectedEvaluationProblem basis (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).InFP :=
  evaluation_inFP_of_connected basis _ _ _ (connected_supportBlocks_inFP basis M hs w h)

/-- Source3.5's final implication, with genuine raw-word promised FP hypotheses
for all numerical support-component problems. It holds for arbitrary signed
symmetric field matrices and arbitrary backgrounds, hence in particular for
positive source weights. No full-source evaluator or cost bound is assumed. -/
theorem supportBlocks_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j=M j i) (w : C → K)
    (h : ∀ c : (colorSupport M hs).ConnectedComponent,
      (evaluationProblem basis (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).InFP :=
  supportBlocks_inFP_of_connected basis M hs w (fun c => connectedEvaluation_inFP_of_all basis _ _ _ (h c))

end PlanarHom.RootedRestriction
