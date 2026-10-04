import PlanarHom.HammingPottsIsolationReduction
import PlanarHom.HammingPottsRecoveryReduction

/-! NEW complete literal size-selected Potts-to-original-source reduction.
No target availability, root-recovery program or hardness premise is assumed. -/
noncomputable section
namespace PlanarHom.HammingPottsToSource
open Complexity Complexity.MixedCode FiniteLanguageAliases
open HammingPottsProductIdentities HammingPottsFieldFamily CartesianGeometry
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q d bt ut dimension : ℕ}

def toJointTarget (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (B : Matrix (Fin q) (Fin q) K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1=>B) (fun u : Fin 0=>u.elim0) (fun _=>1))
      (evaluationProblem basis (appendOne M B) U (fun _=>1)) := by
  have rb : PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1=>B) U (fun _=>1))
      (evaluationProblem basis (appendOne M B) U (fun _=>1)) := by
    simpa only [Function.comp_def,appendOne_aux] using
      binaryRelabelReduction basis (fun _ : Fin 1=>Fin.last bt) (appendOne M B) U (fun _=>1)
  have ru:=unaryRelabelReduction basis (fun u : Fin 0=>u.elim0)
    (fun _ : Fin 1=>B) U (fun _=>1)
  have he : U ∘ (fun u : Fin 0=>u.elim0) = (fun u : Fin 0=>u.elim0) := by
    funext u
    exact u.elim0
  rw [he] at ru
  exact ru.trans rb

/-- Section 6's exact Potts reduction for every occurring clique size.
It composes literal tensor recovery, label embedding and polynomial isolation. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (DistanceKernelAvailability.graph (M old)).Connected)
    (hedge : ∀i j,(DistanceKernelAvailability.graph (M old)).Adj i j→
      0<EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (sizes : Fin d→ℕ) (hsizes : ∀r,2≤sizes r)
    (e : DistanceKernelAvailability.graph (M old) ≃g hammingGraph (fun r=>Fin (sizes r)))
    (s : ℕ) (hs : 2≤s) (hoccurs : ∃r,sizes r=s) :
    PromisePolyTimeTuringReduction (FullLogarithmicPottsReduction.pottsProblem basis s)
      (evaluationProblem basis M U (fun _=>1)) :=
  (HammingPottsRecoveryReduction.reduction basis sizes
    (fun r=>lt_of_lt_of_le (by decide : 0<2) (hsizes r)) s hoccurs e.toEquiv).trans
    ((toJointTarget basis M U (targetK sizes s e.toEquiv)).trans
      (HammingPottsIsolationReduction.reduction basis M U old hA hG hedge sizes hsizes e s hs))

end PlanarHom.HammingPottsToSource
