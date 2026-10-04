import PlanarHom.IntegerTensorObstruction
import PlanarHom.Boolean
import Mathlib.Data.Rat.Cast.Order

/-! NEW literal integer-Ising tensor obstruction. Single-coordinate entries
supply the rational parameters; all subset entries prevent cross-coordinate
cancellation of denominators. This is the numerical contradiction in §7. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.IntegerTensorObstruction
variable {I : Type} [Fintype I] [Nonempty I]

theorem rational_impossible (n : ℕ) (hn : 0<n) (ρ : I → ℚ)
    (hρ : ∀i,0<ρ i ∧ ρ i<1)
    (hinteger : ∀S : Finset I,∃m:ℕ,(n:ℝ)*(∏i∈S,(ρ i:ℝ))=(m:ℝ))
    (hrow : (n:ℝ)=∏i,(1+(ρ i:ℝ))) : False := by
  let a := fun i=>(ρ i).num.natAbs
  let b := fun i=>(ρ i).den
  have ha : ∀i,0<a i := fun i=>Int.natAbs_pos.mpr (Rat.num_pos.mpr (hρ i).1).ne'
  have hrepr : ∀i,(a i:ℝ)/(b i:ℝ)=(ρ i:ℝ) := by
    intro i
    have hi : ((ρ i).num.natAbs:ℤ)=(ρ i).num :=
      Int.natAbs_of_nonneg (Rat.num_pos.mpr (hρ i).1).le
    have hir : ((ρ i).num.natAbs:ℝ)=((ρ i).num:ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ=>(z:ℝ)) hi
    rw [show (a i:ℝ)=((ρ i).num:ℝ) from hir]
    exact (Rat.cast_def (ρ i)).symm
  have hab : ∀i,a i<b i := by
    intro i
    have hb : 0<(b i:ℝ) := by exact_mod_cast (ρ i).pos
    have hx : (ρ i:ℝ)<1 := by exact_mod_cast (hρ i).2
    rw [←hrepr i] at hx
    exact_mod_cast (div_lt_one hb).mp hx
  exact impossible n hn a b ha hab (fun i=>(ρ i).reduced)
    (fun S=>by simpa only [hrepr] using hinteger S)
    (by simpa only [hrepr] using hrow)

end PlanarHom.IntegerTensorObstruction
namespace PlanarHom.IntegerIsingTensorObstruction
open Boolean

theorem tensor_subset {d : ℕ} (ρ : Fin d → ℝ) (S : Finset (Fin d)) :
    tensor ρ (fun _=>false) (fun i=>decide (i∈S))=∏i∈S,ρ i := by
  have hf (i : Fin d) : W (ρ i) false (decide (i∈S))=if i∈S then ρ i else 1 := by
    by_cases hi : i∈S <;> simp [W,hi]
  simp only [tensor]
  simp_rw [hf]
  simp

theorem impossible {d : ℕ} (hd : 0<d) (n : ℕ) (hn : 0<n) (ρ : Fin d → ℝ)
    (hρ : ∀i,0<ρ i ∧ ρ i<1)
    (hinteger : ∀x : Cube d,∃m:ℕ,(n:ℝ)*tensor ρ (fun _=>false) x=(m:ℝ))
    (hrow : (n:ℝ)=∏i,(1+ρ i)) : False := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hsingle : ∀i:Fin d,∃m:ℕ,(n:ℝ)*ρ i=(m:ℝ) := by
    intro i
    simpa only [tensor_unitBit] using hinteger (unitBit i)
  choose a ha using hsingle
  let τ : Fin d → ℚ := fun i=>(a i:ℚ)/(n:ℚ)
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hτ : ∀i,(τ i:ℝ)=ρ i := by
    intro i
    simp only [τ,Rat.cast_div,Rat.cast_natCast]
    apply (div_eq_iff hnR).mpr
    simpa only [mul_comm] using (ha i).symm
  have hτrange : ∀i,0<τ i ∧ τ i<1 := by
    intro i
    constructor
    · have h : 0<(τ i:ℝ) := by rw [hτ]; exact (hρ i).1
      exact_mod_cast h
    · have h : (τ i:ℝ)<1 := by rw [hτ]; exact (hρ i).2
      exact_mod_cast h
  apply IntegerTensorObstruction.rational_impossible n hn τ hτrange
  · intro S
    have h := hinteger (fun i=>decide (i∈S))
    simpa only [hτ,tensor_subset] using h
  · simpa only [hτ] using hrow

end PlanarHom.IntegerIsingTensorObstruction
