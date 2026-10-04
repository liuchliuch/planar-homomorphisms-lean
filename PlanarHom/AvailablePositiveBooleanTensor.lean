import PlanarHom.CommonCubeChartKernels
import PlanarHom.PositiveBooleanDamping

/-! NEW same-chart classification of every positive family member, without a
positive-definiteness premise. Actual rational Schur damping supplies a PD
member; the fixed chart and parallel closure let one undo that damping exactly. -/
noncomputable section
open Classical
namespace PlanarHom.ClosedMatrixFamily.CommonCubeChart
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open LogarithmicSupport BooleanTensorSourceAssembly PositiveBooleanDamping MatrixCoordinateTransport
variable {q:ℕ} {S:Set (Matrix (Fin q) (Fin q) ℝ)}

theorem positive_tensor_of_biased_foundation (W:CommonCubeChart S)
    (hbiased:BiasedBooleanFoundation) (hA:AlgebraicSourceClosed S)
    (htransfer:EffectiveSpectralClosed S) (hgadget:MixedPlanarGadgetClosed S)
    (P:PromiseProblem)
    (havail:∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hnot:¬PromisedSharpPHard P) (N:Matrix (Fin q) (Fin q) ℝ) (hN:N∈S)
    (hpos:∀i j,0<N i j) :
    ∃γ:ℝ,∃ρ:Fin W.dimension→ℝ,0<γ ∧ (∀r,0<ρ r) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ := by
  let G:=logSupport W.maximum
  have hG:G.Connected:=logSupport_connected W.admissible.posDef W.admissible.connected
  obtain ⟨t,ht,ht1,hpd,hdpos⟩:=exists_rational_posDef G hG N (hA.symmetric N hN) hpos
  let D:=damped G N (t:ℝ)
  have hkernel:W.kernel t∈S:=W.kernel_mem hA htransfer t
  have hD:D∈S:=hA.toSpectralParallelClosed.entrywiseProduct_mem N hN _ hkernel
  letI:Nonempty (Fin q):=W.admissible.connected.nonempty
  have hconn:(offDiagonalSupport D hpd.1).Connected:=support_connected_of_positive_entries D hpd.1 hdpos
  have hadm:Admissible S D:=⟨hD,fun i j=>(hdpos i j).le,hpd,hconn⟩
  obtain ⟨γ,ρ,hγ,_,hρ,hform⟩:=W.connected_tensor_of_biased_foundation hbiased hA htransfer
    hgadget P havail hnot D hadm
  have hreindex:Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv D=
      fun i j=>(Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N) i j*
        Boolean.tensor (fun _=>(t:ℝ)) i j:=by
    funext i j
    have hk:=congrFun (congrFun (W.reindex_kernel t) i) j
    change N (W.graphIso.symm i) (W.graphIso.symm j)*
        W.kernel t (W.graphIso.symm i) (W.graphIso.symm j)=_
    rw [show W.kernel t (W.graphIso.symm i) (W.graphIso.symm j)=
      Boolean.tensor (fun _=>(t:ℝ)) i j from hk]
    rfl
  rw [hreindex] at hform
  refine ⟨γ,(fun r=>ρ r/(t:ℝ)),hγ,fun r=>div_pos (hρ r).1 (by exact_mod_cast ht),?_⟩
  exact undo_tensor _ (t:ℝ) (by exact_mod_cast ht) γ ρ hform

end PlanarHom.ClosedMatrixFamily.CommonCubeChart
