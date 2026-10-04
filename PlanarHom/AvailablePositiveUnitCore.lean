import PlanarHom.AvailablePositiveBooleanTensor
import PlanarHom.PositiveUnitDiagonalRigidity

/-! NEW normalized positive-core consequence in the existing source chart.
The independent biased Boolean hardness input remains explicit. -/
noncomputable section
open Classical
namespace PlanarHom.ClosedMatrixFamily.CommonCubeChart
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open BooleanTensorSourceAssembly
variable {q:ℕ} {S:Set (Matrix (Fin q) (Fin q) ℝ)}

theorem positive_unit_core_of_biased_foundation (W:CommonCubeChart S)
    (hbiased:BiasedBooleanFoundation) (hA:AlgebraicSourceClosed S)
    (htransfer:EffectiveSpectralClosed S) (hgadget:MixedPlanarGadgetClosed S)
    (P:PromiseProblem)
    (havail:∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hnot:¬PromisedSharpPHard P) (N:Matrix (Fin q) (Fin q) ℝ) (hN:N∈S)
    (hpos:∀i j,0<N i j) (hdiag:∀i,N i i=1) (hinj:Function.Injective N) :
    ∃ρ:Fin W.dimension→ℝ,(∀r,0<ρ r ∧ ρ r≠1) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=Boolean.tensor ρ ∧ IsUnit N := by
  obtain ⟨γ,ρ,hγ,hρ,he⟩:=W.positive_tensor_of_biased_foundation hbiased hA htransfer hgadget P havail hnot N hN hpos
  let e:=W.graphIso.toEquiv
  have hγ1:γ=1:=by
    have h:=congrFun (congrFun he (fun _=>false)) (fun _=>false)
    change N (e.symm (fun _=>false)) (e.symm (fun _=>false))=γ*Boolean.tensor ρ (fun _=>false) (fun _=>false) at h
    simpa only [hdiag,Boolean.tensor_diag,mul_one] using h.symm
  have he':Matrix.reindex e e N=Boolean.tensor ρ:=by simpa only [hγ1,one_smul] using he
  have hi:Function.Injective (Matrix.reindex e e N):=by
    intro i j hij
    apply e.symm.injective
    apply hinj
    funext k
    have h:=congrFun hij (e k)
    simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply] using h
  have hn:∀r,ρ r≠1:=PositiveUnitDiagonalRigidity.tensor_parameters_nonunit ρ (he' ▸ hi)
  have hu:IsUnit (Matrix.reindex e e N):=by
    rw [he']
    exact (Boolean.tensor_isUnit_iff_of_pos hρ).mpr hn
  refine ⟨ρ,fun r=>⟨hρ r,hn r⟩,he',?_⟩
  have hb:=hu.map (Matrix.reindexAlgEquiv ℝ ℝ e).symm.toMonoidHom
  change IsUnit ((Matrix.reindexAlgEquiv ℝ ℝ e).symm ((Matrix.reindexAlgEquiv ℝ ℝ e) N)) at hb
  simpa only [AlgEquiv.symm_apply_apply] using hb

end PlanarHom.ClosedMatrixFamily.CommonCubeChart
