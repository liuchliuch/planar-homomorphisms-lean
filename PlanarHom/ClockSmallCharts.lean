import PlanarHom.ClockMatrixObstruction
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
open Classical
namespace PlanarHom.ClockModel
open Boolean

def twoChart : Fin 2≃Cube 1 := finTwoEquiv.trans (Equiv.funUnique _ _).symm

def grayPair : Fin 4≃Bool×Bool where
  toFun:=![(false,false),(false,true),(true,true),(true,false)]
  invFun:=fun p=>if p.1 then (if p.2 then 2 else 3) else (if p.2 then 1 else 0)
  left_inv:=by intro i; fin_cases i <;> rfl
  right_inv:=by rintro ⟨x,y⟩; cases x <;> cases y <;> rfl

def fourChart : Fin 4≃Cube 2 := grayPair.trans (finTwoArrowEquiv Bool).symm

theorem angle_two (i:Fin 2) : angle 2 i=![0,Real.pi] i := by
  fin_cases i <;> norm_num [angle] <;> ring

theorem angle_four (i:Fin 4) : angle 4 i=![0,Real.pi/2,Real.pi,Real.pi+Real.pi/2] i := by
  fin_cases i <;> norm_num [angle] <;> ring

theorem cos_two (i:Fin 2) : Real.cos (angle 2 i)=![1,-1] i := by
  rw [angle_two]; fin_cases i <;> simp

theorem sin_two (i:Fin 2) : Real.sin (angle 2 i)=![0,0] i := by
  rw [angle_two]; fin_cases i <;> simp

theorem cos_four (i:Fin 4) : Real.cos (angle 4 i)=![1,0,-1,0] i := by
  rw [angle_four]; fin_cases i <;> simp [Real.cos_add]

theorem sin_four (i:Fin 4) : Real.sin (angle 4 i)=![0,1,0,-1] i := by
  rw [angle_four]; fin_cases i <;> simp [Real.sin_add]

theorem two_tensor (K:ℝ) (i j:Fin 2) :
    interaction 2 K i j=Real.exp K*tensor (fun _:Fin 1=>Real.exp (-2*K)) (twoChart i) (twoChart j) := by
  simp only [interaction,Real.cos_sub,cos_two,sin_two]
  fin_cases i <;> fin_cases j <;>
    simp [tensor,twoChart,finTwoEquiv,W,←Real.exp_add] <;> congr 1 <;> ring

theorem four_tensor (K:ℝ) (i j:Fin 4) :
    interaction 4 K i j=Real.exp K*tensor (fun _:Fin 2=>Real.exp (-K)) (fourChart i) (fourChart j) := by
  simp only [interaction,Real.cos_sub,cos_four,sin_four]
  fin_cases i <;> fin_cases j <;>
    simp [tensor,fourChart,grayPair,finTwoArrowEquiv,W,Fin.prod_univ_two,←Real.exp_add] <;> congr 1 <;> ring

theorem exp_parameter_nonunit {K:ℝ} (hK:K≠0) (a:ℝ) (ha:a≠0) : Real.exp (a*K)≠1 := by
  intro h
  have hz:a*K=0:=Real.exp_injective (by simpa only [Real.exp_zero] using h)
  exact hK ((mul_eq_zero.mp hz).resolve_left ha)

end PlanarHom.ClockModel
