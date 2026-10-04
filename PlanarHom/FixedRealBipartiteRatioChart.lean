import PlanarHom.FixedRealBipartiteEvaluation

/-! NEW source-entry chart for unequal bipartite rank-two tensor blocks.
Every amplitude and Ising parameter belongs to the original represented field. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealGraphEvaluation
open BooleanTensorEasyAssembly BipartiteRankTwoTractability
variable {K C:Type} [Field K] [Fintype C] {k l d:ℕ}

 theorem bipartite_ratios (φ:K→+*ℝ) (M:Matrix C C K) (i0:Fin k) (j0:Fin l)
    (e:C≃(Fin k⊕Fin l)×Boolean.Cube d) (a:Fin k→ℝ) (b:Fin l→ℝ)
    (ha:∀i,0<a i) (hb:∀j,0<b j) (ρ:Fin d→ℝ)
    (hsource:Matrix.reindex e e (fun i j=>φ (M i j))=
      MultiGraph.tensorInteraction (matrix a b) (Boolean.tensor ρ)) :
    ∃α:Fin k→K,∃β:Fin l→K,∃p:Fin d→K,
      ∀i j,M i j=MultiGraph.tensorInteraction (matrix α β)
        (BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r))) (e i) (e j) := by
  let z:Boolean.Cube d:=fun _=>false
  have he (p r:(Fin k⊕Fin l)×Boolean.Cube d):
      φ (M (e.symm p) (e.symm r))=matrix a b p.1 r.1*Boolean.tensor ρ p.2 r.2:=
    congrArg (fun A:Matrix _ _ ℝ=>A p r) hsource
  let γ:=M (e.symm (.inl i0,z)) (e.symm (.inr j0,z))
  let α:Fin k→K:=fun i=>M (e.symm (.inl i,z)) (e.symm (.inr j0,z))
  let β:Fin l→K:=fun j=>M (e.symm (.inl i0,z)) (e.symm (.inr j,z))/γ
  let p:Fin d→K:=fun r=>M (e.symm (.inl i0,z)) (e.symm (.inr j0,Boolean.unitBit r))/γ
  have hγ:φ γ=a i0*b j0:=by simp only [γ,he,matrix_inl_inr,Boolean.tensor_diag,mul_one]
  have ha0:a i0≠0:=(ha i0).ne'
  have hb0:b j0≠0:=(hb j0).ne'
  have hα (i:Fin k):φ (α i)=a i*b j0:=by
    simp only [α,he,matrix_inl_inr,Boolean.tensor_diag,mul_one]
  have hβ (j:Fin l):φ (β j)=b j/b j0:=by
    change φ (M (e.symm (.inl i0,z)) (e.symm (.inr j,z))/γ)=_
    rw [map_div₀,he,hγ]
    simp only [matrix_inl_inr,Boolean.tensor_diag,mul_one]
    field_simp [ha0,hb0]
  have hp (r:Fin d):φ (p r)=ρ r:=by
    change φ (M (e.symm (.inl i0,z)) (e.symm (.inr j0,Boolean.unitBit r))/γ)=_
    rw [map_div₀,he,hγ]
    simp only [matrix_inl_inr,z,Boolean.tensor_unitBit]
    field_simp [ha0,hb0]
  have hpair (i:Fin k) (j:Fin l):φ (α i)*φ (β j)=a i*b j:=by
    rw [hα,hβ]
    field_simp [hb0]
  have hT (x y:Boolean.Cube d):
      φ (BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r)) x y)=Boolean.tensor ρ x y:=by
    simp [BooleanTensorSpectral.tensor,Boolean.tensor,isingMatrix,Boolean.W,map_prod,apply_ite,hp]
  have hB (x y:(Fin k⊕Fin l)×Boolean.Cube d):
      φ (MultiGraph.tensorInteraction (matrix α β)
        (BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r))) x y)=
      matrix a b x.1 y.1*Boolean.tensor ρ x.2 y.2:=by
    rcases x with ⟨x,u⟩
    rcases y with ⟨y,v⟩
    cases x <;> cases y <;> simp [MultiGraph.tensorInteraction,matrix,hT,hpair]
  refine ⟨α,β,p,?_⟩
  intro i j
  apply φ.injective
  have hij:=he (e i) (e j)
  simp only [e.symm_apply_apply] at hij
  exact hij.trans (hB (e i) (e j)).symm

end PlanarHom.FixedRealGraphEvaluation
