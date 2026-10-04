import PlanarHom.Boolean
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Shared finite algebra for coupled Ising systems: real signs of binary
linear functionals and exact character orthogonality on any finite binary
vector space. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BinaryCharacters
abbrev F₂ := ZMod 2

def sign (z:F₂) : ℝ := if z=0 then 1 else -1

@[simp] theorem sign_zero : sign 0=1 := by simp [sign]
@[simp] theorem sign_one : sign 1= -1 := by norm_num [sign]
theorem sign_add (x y:F₂) : sign (x+y)=sign x*sign y := by
  fin_cases x <;> fin_cases y <;> norm_num [sign,show (1+1:F₂)=0 by decide]
@[simp] theorem sign_square (x:F₂) : sign x*sign x=1 := by
  fin_cases x <;> norm_num [sign]
theorem sign_injective : Function.Injective sign := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | norm_num [sign] at h

def bitEquiv : F₂≃Bool := (ZMod.finEquiv 2).symm.toEquiv.trans finTwoEquiv

@[simp] theorem bitEquiv_zero : bitEquiv 0=false := rfl
@[simp] theorem bitEquiv_one : bitEquiv 1=true := rfl

abbrev Space (n:ℕ) := Fin n→F₂

def functional {n:ℕ} (a:Space n) : Space n→ₗ[F₂]F₂ where
  toFun:=fun x=>∑i,a i*x i
  map_add':=by intro x y; simp [mul_add,Finset.sum_add_distrib]
  map_smul':=by intro c x; simp [Finset.mul_sum,mul_left_comm]

theorem functional_injective {n:ℕ} : Function.Injective (functional (n:=n)) := by
  intro a b h
  funext i
  have hh:=LinearMap.congr_fun h (Pi.single i 1)
  simpa [functional,Pi.single_apply] using hh

variable {X:Type} [AddCommGroup X] [Module F₂ X] [Fintype X]

def character (l:X→ₗ[F₂]F₂) (x:X) : ℝ := sign (l x)

@[simp] theorem character_zero (x:X) : character (0:X→ₗ[F₂]F₂) x=1 := rfl

theorem character_add (l:X→ₗ[F₂]F₂) (x y:X) :
    character l (x+y)=character l x*character l y := by
  simp only [character,map_add,sign_add]

theorem character_sum_zero (l:X→ₗ[F₂]F₂) (hl:l≠0) : ∑x,character l x=0 := by
  have hx:∃x,l x≠0 := by
    by_contra h
    apply hl
    ext x
    exact not_not.mp (fun hx=>h ⟨x,hx⟩)
  obtain ⟨t,ht⟩:=hx
  have ht':sign (l t)= -1:=by simp [sign,ht]
  have hsum : (∑x,character l x)=(∑x,character l (x+t)) := by
    exact (Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _=>rfl)).symm
  simp only [character,map_add,sign_add,←Finset.sum_mul,ht'] at hsum
  change (∑x,sign (l x))=0
  linarith

theorem character_orthogonality (l k:X→ₗ[F₂]F₂) :
    (∑x,character l x*character k x)=if l=k then (Fintype.card X:ℝ) else 0 := by
  by_cases h:l=k
  · subst k; simp [character,sign_square]
  · rw [if_neg h]
    have hne:l+k≠0 := by
      intro he
      apply h
      ext x
      have hh:=LinearMap.congr_fun he x
      change l x+k x=0 at hh
      have he:∀a b:F₂,a+b=0→a=b:=by decide
      exact he _ _ hh
    have hh:=character_sum_zero (l+k) hne
    simpa only [character,LinearMap.add_apply,sign_add] using hh

end PlanarHom.BinaryCharacters
