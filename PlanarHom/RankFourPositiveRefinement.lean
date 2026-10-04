import PlanarHom.RankFourClassification
import PlanarHom.ThreeStatePositiveRank

noncomputable section
open Classical
namespace PlanarHom.RankFour
open Boolean Structures

theorem tensor_parameters_nonunit {C:Type} {d:ℕ} {M:Matrix C C ℝ}
    (hi:LinearIndependent ℝ M) (γ:ℝ) (ρ:Fin d→ℝ) (e:C≃Cube d)
    (hm:∀i j,M i j=γ*tensor ρ (e i) (e j)) : ∀r,ρ r≠1 := by
  intro r hr
  let x:Cube d:=fun _=>false
  let y:Cube d:=fun s=>if s=r then true else false
  have he : M (e.symm x)=M (e.symm y) := by
    funext j
    simp only [hm,Equiv.apply_symm_apply]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    by_cases hsr:s=r
    · subst s; simp [x,y,hr]
    · simp [x,y,hsr]
  have he' := e.symm.injective (hi.injective he)
  have hh:=congrFun he' r
  simp [x,y] at hh

def PositiveFourTensor (M:Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃(γ:ℝ)(ρ:Fin 2→ℝ)(e:Fin 4≃Cube 2),0<γ ∧
    (∀r,0<ρ r ∧ ρ r≠1) ∧ ∀i j,M i j=γ*tensor ρ (e i) (e j)

theorem positive_nonnegativeClass_iff_tensor {M:Matrix (Fin 4) (Fin 4) ℝ}
    (hp:∀i j,0<M i j) (hr:M.rank=4) : NonnegativeClass M ↔ PositiveFourTensor M := by
  constructor
  · intro h
    have ha:=ThreeStateDimension.positive_class_allowed hp h
    rcases allowedBlock_singleTensor (Fintype.card_fin 4) hr ha with
      ⟨γ,ρ,e,hγ,hρ,hm⟩|⟨γ,ρ,e,hγ,hρ,hm⟩
    · exact ⟨γ,ρ,e,hγ,fun r=>⟨hρ r,tensor_parameters_nonunit
        (rows_independent (by simpa only [Fintype.card_fin] using hr)) γ ρ e hm r⟩,hm⟩
    · have hz : M 0 0=0 := by simp [hm,swap]
      linarith [hp 0 0]
  · rintro ⟨γ,ρ,e,hγ,hρ,hm⟩
    exact SingleTensor.nonnegativeClass (Or.inl ⟨γ,ρ,e,hγ,fun r=>(hρ r).1,hm⟩)

end PlanarHom.RankFour
