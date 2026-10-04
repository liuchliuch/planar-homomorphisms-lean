import PlanarHom.PositiveBooleanDamping
import PlanarHom.BooleanMatrix

/-! NEW source-compatible damping interface. A single actual positive rational
PD damping proves the claimed tensor form; no limiting target form is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveSymmetricTensorDamping
variable {d:ℕ}

def damped (B:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (t:ℝ) :
    Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ:=fun i j=>B i j*Boolean.tensor (fun _=>t) i j

theorem damped_eq_graph (B:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (t:ℝ) :
    damped B t=PositiveBooleanDamping.damped (Boolean.cubeGraph d) B t := by
  have hk:=Boolean.cubeGraph_distanceKernel_eq_tensor (d:=d) t
  funext i j
  rw [damped,←hk]
  rfl

theorem tensor_of_positive_definite_dampings
    (B:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (hB:B.IsHermitian) (hpos:∀i j,0<B i j)
    (hclass:∀t:ℚ,0<t→t<1→(damped B (t:ℝ)).PosDef→
      ∃γ:ℝ,∃ρ:Fin d→ℝ,0<γ ∧ (∀i,0<ρ i) ∧ damped B (t:ℝ)=γ • Boolean.tensor ρ) :
    ∃γ:ℝ,∃ρ:Fin d→ℝ,0<γ ∧ (∀i,0<ρ i) ∧ B=γ • Boolean.tensor ρ := by
  obtain ⟨t,ht,ht1,hpd,_⟩:=PositiveBooleanDamping.exists_rational_posDef
    (Boolean.cubeGraph d) (Boolean.cubeGraph_connected d) B hB hpos
  rw [←damped_eq_graph] at hpd
  obtain ⟨γ,ρ,hγ,hρ,he⟩:=hclass t ht (by exact_mod_cast ht1) hpd
  refine ⟨γ,(fun i=>ρ i/(t:ℝ)),hγ,fun i=>div_pos (hρ i) (by exact_mod_cast ht),?_⟩
  exact PositiveBooleanDamping.undo_tensor B (t:ℝ) (by exact_mod_cast ht) γ ρ he

end PlanarHom.PositiveSymmetricTensorDamping
