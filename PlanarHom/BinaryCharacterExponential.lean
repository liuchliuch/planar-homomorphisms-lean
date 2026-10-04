import PlanarHom.BinaryCharacterKernelRank
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BinaryCharacters
variable {X:Type} [AddCommGroup X] [Module F₂ X] [Fintype X] {m:ℕ}

def interaction (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) : Matrix X X ℝ :=
  fun x y=>Real.exp (kernel l J x y)

theorem kernel_fourier (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (J:Fin m→ℝ) (x:X) (r:Fin m) :
    (∑z,kernel l J x z*character (l r) z)=J r*character (l r) x*(Fintype.card X:ℝ) := by
  simp only [kernel,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc,←Finset.mul_sum,character_orthogonality]
  simp [hl.eq_iff]

theorem equal_rows_iff (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (x y:X) :
    interaction l J x=interaction l J y ↔ ∀r,l r x=l r y := by
  constructor
  · intro h r
    have hh:kernel l J x=kernel l J y := by
      funext z
      exact Real.exp_injective (congrFun h z)
    have he:=congrArg (fun v:X→ℝ=>∑z,v z*character (l r) z) hh
    dsimp only at he
    rw [kernel_fourier l hl J x r,kernel_fourier l hl J y r] at he
    have hn:(Fintype.card X:ℝ)≠0:=ne_of_gt (by exact_mod_cast Fintype.card_pos)
    have hc:=mul_left_cancel₀ (hJ r) (mul_right_cancel₀ hn he)
    exact sign_injective hc
  · intro h
    funext z
    simp only [interaction,kernel,character,h]

theorem interaction_symmetric (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) (x y:X) :
    interaction l J x y=interaction l J y x := by
  unfold interaction; congr 1
  apply Finset.sum_congr rfl
  intro r hr; ring

theorem interaction_diagonal (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) (x:X) :
    interaction l J x x=Real.exp (∑r,J r) := by
  simp only [interaction,kernel,character,mul_assoc,sign_square,mul_one]

end PlanarHom.BinaryCharacters
