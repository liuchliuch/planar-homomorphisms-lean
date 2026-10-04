import PlanarHom.BooleanTensorSourceAssembly
import PlanarHom.CommonCubeChartBasicConsequences
import PlanarHom.AvailableClosedFamilyCube

/-! NEW same-chart consequence of the actual Boolean source reduction. The
independent biased Boolean foundation is explicit; there is no target-shape or
factor-equality assumption. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ClosedMatrixFamily.CommonCubeChart
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open LogarithmicSupport Boolean CubeTensorExponential BooleanTensorSourceAssembly
variable {q:ℕ} {S:Set (Matrix (Fin q) (Fin q) ℝ)}

theorem connected_tensor_of_biased_foundation (W:CommonCubeChart S)
    (hbiased:BiasedBooleanFoundation) (hA:AlgebraicSourceClosed S)
    (htransfer:EffectiveSpectralClosed S) (hgadget:MixedPlanarGadgetClosed S)
    (P:PromiseProblem)
    (havail:∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hnot:¬PromisedSharpPHard P) (N:Matrix (Fin q) (Fin q) ℝ) (hN:Admissible S N) :
    ∃γ:ℝ,∃ρ:Fin W.dimension→ℝ,0<γ ∧ IsAlgebraic ℚ γ ∧
      (∀r,0<ρ r ∧ ρ r<1 ∧ IsAlgebraic ℚ (ρ r)) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ := by
  obtain ⟨he,hγ,hγalg,hf,hconn⟩:=proposition48 S hA htransfer hgadget W.maximum W.admissible
    W.isMaximum W.positive_log W.graphIso N hN.mem hN.posDef hN.nonneg
  let e:=W.graphIso.toEquiv
  let γ:=N (W.graphIso.symm zeroColor) (W.graphIso.symm zeroColor)
  let F:=factorInCoordinates e N
  have hpos:∀r i j,0<F r i j:=hconn.mp hN.connected
  have hsource:Matrix.reindex e e N=γ • CubeTensorExponential.tensor F:=by
    ext i j
    have h:=he (e.symm i) (e.symm j)
    change N (e.symm i) (e.symm j)=γ*∏r,F r (e (e.symm i) r) (e (e.symm j) r) at h
    change N (e.symm i) (e.symm j)=γ*∏r,F r (i r) (j r)
    simpa only [Equiv.apply_symm_apply] using h
  have hdiag:∀r,F r false false=F r true true:=by
    intro r
    by_contra hr
    let L:=unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN.mem)
    have hard:=scaled_tensor_hard_of_foundation hbiased L (fun _=>rfl) 0 e F
      (fun r=>(hf r).1) hpos (fun r=>(hf r).2.2.1) γ hγ hγalg hsource ⟨r,hr⟩
    obtain ⟨sim⟩:=havail N hN.mem
    exact hnot (hard.trans sim)
  let ρ:=fun r=>F r false true
  have hfactor:∀r,F r=Boolean.W (ρ r):=by
    intro r
    have hff:F r false false=1:=(hf r).2.2.2
    have htt:F r true true=1:=(hdiag r).symm.trans hff
    have hsym:F r true false=F r false true:=by
      simpa only [star_trivial] using (hf r).1.1.apply false true
    ext i j
    cases i <;> cases j <;> simp [Boolean.W,hff,htt,hsym,ρ]
  have hrho:∀r,0<ρ r ∧ ρ r<1 ∧ IsAlgebraic ℚ (ρ r):=by
    intro r
    have hdet:=BooleanPDNormalization.offDiagonal_sq_lt_diagonal_product (F r) (hf r).1
    have hff:F r false false=1:=(hf r).2.2.2
    rw [←hdiag r,hff] at hdet
    exact ⟨hpos r false true,by dsimp [ρ];nlinarith [hpos r false true],(hf r).2.2.1 false true⟩
  refine ⟨γ,ρ,hγ,hγalg,hrho,?_⟩
  rw [hsource]
  congr 1
  funext i j
  apply Finset.prod_congr rfl
  intro r _
  exact congrFun (congrFun (hfactor r) (i r)) (j r)

end PlanarHom.ClosedMatrixFamily.CommonCubeChart
