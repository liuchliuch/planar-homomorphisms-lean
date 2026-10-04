import PlanarHom.RankFourSumClosure
import PlanarHom.RankFourSingleBlock
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C : Type}

theorem AllowedBlock.posScalar {M : Matrix C C ℝ} (h:AllowedBlock M)
    (γ:ℝ) (hγ:0<γ) : AllowedBlock (fun i j=>γ*M i j) := by
  have hsq : Real.sqrt γ*Real.sqrt γ=γ := Real.mul_self_sqrt hγ.le
  have hpos : 0<Real.sqrt γ := Real.sqrt_pos.mpr hγ
  cases h with
  | zero e hz => exact .zero e (fun i j=>by rw [hz,mul_zero])
  | positive k d hk a ρ ha hρ e hm =>
    refine .positive k d hk (fun i=>Real.sqrt γ*a i) ρ (fun i=>mul_pos hpos (ha i)) hρ e ?_
    intro i j; rw [hm]; nth_rw 1 [←hsq]; ring
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    refine .bipartite k l d hk hl (fun i=>Real.sqrt γ*a i) (fun i=>Real.sqrt γ*b i) ρ
      (fun i=>mul_pos hpos (ha i)) (fun i=>mul_pos hpos (hb i)) hρ e ?_
    intro i j; rw [hm]
    cases (e i).1 <;> cases (e j).1 <;> simp only [bipartiteAmplitude]
    · ring
    · nth_rw 1 [←hsq]; ring
    · nth_rw 1 [←hsq]; ring
    · ring

theorem NonnegativeClass.posScalar {M : Matrix C C ℝ} (h:NonnegativeClass M)
    (γ:ℝ) (hγ:0<γ) : NonnegativeClass (fun i j=>γ*M i j) := by
  obtain ⟨t,b,hb,hz,ha⟩:=h
  exact ⟨t,b,hb,fun i j he=>by dsimp only; rw [hz i j he,mul_zero],fun r=>(ha r).posScalar γ hγ⟩

end PlanarHom.Structures
namespace PlanarHom.RankFour
open Structures Boolean
variable {C : Type}

theorem scaled_tensor_allowed {d:ℕ} (γ:ℝ) (hγ:0<γ) (ρ:Fin d→ℝ)
    (hρ:∀r,0<ρ r) (e:C≃Cube d) :
    AllowedBlock (fun i j=>γ*tensor ρ (e i) (e j)) := by
  have hsq := Real.mul_self_sqrt hγ.le
  refine .positive 1 d (by omega) (fun _=>Real.sqrt γ) ρ
    (fun _=>Real.sqrt_pos.mpr hγ) hρ (e.trans (Equiv.uniqueProd _ _).symm) ?_
  intro i j
  simpa only [Equiv.trans_apply,Equiv.uniqueProd_symm_apply] using
    congrArg (fun t=>t*tensor ρ (e i) (e j)) hsq.symm

theorem scaled_swap_tensor_allowed {d:ℕ} (γ:ℝ) (hγ:0<γ) (ρ:Fin d→ℝ)
    (hρ:∀r,0<ρ r) (e:C≃Bool×Cube d) :
    AllowedBlock (fun i j=>γ*swap (e i).1 (e j).1*tensor ρ (e i).2 (e j).2) := by
  let e' := e.trans (Equiv.prodCongr sideEquiv.symm (Equiv.refl _))
  refine .bipartite 1 1 d (by omega) (by omega) (fun _=>γ) (fun _=>1) ρ
    (fun _=>hγ) (fun _=>by norm_num) hρ e' ?_
  intro i j
  cases hxi:(e i).1 <;> cases hxj:(e j).1 <;>
    simp [e',sideEquiv,swap,bipartiteAmplitude,hxi,hxj]

theorem SingleTensor.nonnegativeClass {M : Matrix C C ℝ} (h:SingleTensor M) :
    NonnegativeClass M := by
  rcases h with ⟨γ,ρ,e,hγ,hρ,hm⟩|⟨γ,ρ,e,hγ,hρ,hm⟩
  · have he : M=(fun i j=>γ*tensor ρ (e i) (e j)) := funext (fun i=>funext (hm i))
    rw [he]; exact (scaled_tensor_allowed γ hγ ρ hρ e).nonnegativeClass
  · let ep := e.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) Bool).symm)
    have h := scaled_swap_tensor_allowed γ hγ (fun _:Fin 1=>ρ) (fun _=>hρ) ep
    apply AllowedBlock.nonnegativeClass
    convert h using 1
    funext i j
    simpa [tensor,ep] using hm i j

end PlanarHom.RankFour
