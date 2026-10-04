-- NEW source adapter; tensor/scalar semantic proofs retained from recovered
-- assemble_ising_tensor_tractability/IsingTensorTractabilitySemantics.lean.
-- Missing evaluate_constant dependency replaced by the proved homogeneous identity.
import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.HammingPottsTensorPartition
import PlanarHom.MixedColorEquivalence

/-! Exact tensor and scalar partition identities on the original occurrence
codes. There are no graph restrictions beyond valid labels and endpoints. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorFPClosure
open Complexity Complexity.MixedCode
variable {K C D I : Type} [CommSemiring K] [Fintype C] [Fintype D]
  [Fintype I] [DecidableEq I]

def emptyUnaries : Fin 0 → C → K := fun u => Fin.elim0 u

theorem evaluate_unweighted (g : MixedCode) (hg : g.Valid 1 0) (M : Matrix C C K) :
    g.evaluate hg (fun _ => M) emptyUnaries (fun _ => 1) =
      (g.toMultiGraph hg).unweighted M := by
  exact evaluate_homogeneous g hg M (fun _=>1)

/-- Finite tensor factorization, including the empty tensor and every isolated
vertex, loop and repeated edge occurrence. -/
theorem evaluate_tensor (g : MixedCode) (hg : g.Valid 1 0)
    (A : I → Matrix C C K) :
    g.evaluate hg (fun _ => fun x y : I → C => ∏ i, A i (x i) (y i))
        emptyUnaries (fun _ => 1) =
      ∏ i, g.evaluate hg (fun _ => A i) emptyUnaries (fun _ => 1) := by
  simp only [evaluate_unweighted]
  exact HammingPottsTensorPartition.partition_tensor (g.toMultiGraph hg) A

theorem evaluate_product (g : MixedCode) (hg : g.Valid 1 0)
    (A : Matrix C C K) (B : Matrix D D K) :
    g.evaluate hg (fun _ => MultiGraph.tensorInteraction A B) emptyUnaries (fun _ => 1) =
      g.evaluate hg (fun _ => A) emptyUnaries (fun _ => 1) *
        g.evaluate hg (fun _ => B) emptyUnaries (fun _ => 1) := by
  simp only [evaluate_unweighted]
  exact (g.toMultiGraph hg).unweighted_tensor A B

/-- Scaling one fixed interaction contributes once per edge occurrence,
including loops, and contributes nothing at isolated vertices. -/
theorem evaluate_scalar (g : MixedCode) (hg : g.Valid 1 0)
    (γ : K) (A : Matrix C C K) :
    g.evaluate hg (fun _ => γ • A) emptyUnaries (fun _ => 1) =
      γ ^ g.edges.length * g.evaluate hg (fun _ => A) emptyUnaries (fun _ => 1) := by
  simp only [evaluate_unweighted, MultiGraph.unweighted_eq]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]

end PlanarHom.BooleanTensorFPClosure
