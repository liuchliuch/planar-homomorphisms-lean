import PlanarHom.FixedRealGraphEvaluation
import PlanarHom.BooleanTensorSpectral

/-! NEW original-field positive-block chart. Anchor ratios replace displayed
square-root amplitudes, so the complete algorithm stays in the prescribed
field even when the original real amplitudes lie outside it. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealGraphEvaluation
open BooleanTensorEasyAssembly
variable {K C:Type} [Field K] [Fintype C] {k d:ℕ}

 theorem positive_ratios (φ:K→+*ℝ) (M:Matrix C C K)
    (i0:Fin k) (e:C≃Fin k×Boolean.Cube d) (a:Fin k→ℝ) (ha:∀i,0<a i)
    (ρ:Fin d→ℝ)
    (hsource:Matrix.reindex e e (fun i j=>φ (M i j))=
      fun p r=>a p.1*a r.1*Boolean.tensor ρ p.2 r.2) :
    ∃γ:K,∃α:Fin k→K,∃p:Fin d→K,
      ∀i j,M i j=γ*MultiGraph.tensorInteraction (fun u v=>α u*α v)
        (BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r))) (e i) (e j) := by
  let z:Boolean.Cube d:=fun _=>false
  have he (p r:Fin k×Boolean.Cube d) :
      φ (M (e.symm p) (e.symm r))=a p.1*a r.1*Boolean.tensor ρ p.2 r.2:=
    congrArg (fun A:Matrix _ _ ℝ=>A p r) hsource
  let γ:=M (e.symm (i0,z)) (e.symm (i0,z))
  let α:Fin k→K:=fun i=>M (e.symm (i,z)) (e.symm (i0,z))/γ
  let p:Fin d→K:=fun r=>M (e.symm (i0,z)) (e.symm (i0,Boolean.unitBit r))/γ
  have hγ:φ γ=a i0*a i0:=by simp only [γ,he,Boolean.tensor_diag,mul_one]
  have ha0:a i0≠0:=(ha i0).ne'
  have hα (i:Fin k):φ (α i)=a i/a i0:=by
    change φ (M (e.symm (i,z)) (e.symm (i0,z))/γ)=_
    rw [map_div₀,he,hγ,Boolean.tensor_diag,mul_one]
    field_simp [ha0]
  have hp (r:Fin d):φ (p r)=ρ r:=by
    change φ (M (e.symm (i0,z)) (e.symm (i0,Boolean.unitBit r))/γ)=_
    rw [map_div₀,he,hγ]
    simp only [z,Boolean.tensor_unitBit]
    field_simp [ha0]
  have hT (x y:Boolean.Cube d):
      φ (BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r)) x y)=Boolean.tensor ρ x y:=by
    simp [BooleanTensorSpectral.tensor,Boolean.tensor,isingMatrix,Boolean.W,map_prod,apply_ite,hp]
  refine ⟨γ,α,p,?_⟩
  intro i j
  apply φ.injective
  have hij:=he (e i) (e j)
  simp only [e.symm_apply_apply] at hij
  rw [hij,map_mul,hγ]
  change _=(a i0*a i0)*φ ((α (e i).1*α (e j).1)*
    BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r)) (e i).2 (e j).2)
  rw [map_mul,map_mul,hα,hα,hT]
  field_simp [ha0]
  <;> ring

end PlanarHom.FixedRealGraphEvaluation
