import PlanarHom.TensorDenominatorProduct
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! NEW integer tensor obstruction from §7. All subset entries are retained:
no pairwise-denominator coprimality is assumed. The prime-selected product
lemma supplies the full denominator product bound used in the contradiction. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.IntegerTensorObstruction
variable {I : Type} [Fintype I]

theorem subset_denominator_dvd (n : ℕ) (a b : I → ℕ) (hb : ∀i,0<b i)
    (S : Finset I) (h : ∃m:ℕ,(n:ℝ)*(∏i∈S,(a i:ℝ)/(b i:ℝ))=(m:ℝ)) :
    (∏i∈S,b i) ∣ n*(∏i∈S,a i) := by
  obtain ⟨m,hm⟩ := h
  have hden : (∏i∈S,(b i:ℝ))≠0 := Finset.prod_ne_zero_iff.mpr
    (fun i _=>by exact_mod_cast (hb i).ne')
  have he : (n:ℝ)*(∏i∈S,(a i:ℝ))/(∏i∈S,(b i:ℝ))=(m:ℝ) := by
    simpa only [Finset.prod_div_distrib,mul_div_assoc] using hm
  have hmul := (div_eq_iff hden).mp he
  have heNat : n*(∏i∈S,a i)=m*(∏i∈S,b i) := by exact_mod_cast hmul
  exact ⟨m,heNat.trans (Nat.mul_comm _ _)⟩

theorem impossible [Nonempty I] (n : ℕ) (hn : 0<n) (a b : I → ℕ)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) (hc : ∀i,Nat.Coprime (a i) (b i))
    (hinteger : ∀S : Finset I,∃m:ℕ,(n:ℝ)*(∏i∈S,(a i:ℝ)/(b i:ℝ))=(m:ℝ))
    (hrow : (n:ℝ)=∏i,(1+(a i:ℝ)/(b i:ℝ))) : False := by
  have hb : ∀i,0<b i := fun i=>(ha i).trans (hab i)
  have hdiv := TensorDenominatorProduct.product_dvd n a b hc
    (fun S=>subset_denominator_dvd n a b hb S (hinteger S))
  have hle : (∏i,b i)≤n := Nat.le_of_dvd hn hdiv
  have hfactor : ∀i,1+(a i:ℝ)/(b i:ℝ)<(b i:ℝ) := by
    intro i
    have hb0 : 0<(b i:ℝ) := by exact_mod_cast hb i
    have ha' : (a i:ℝ)<(b i:ℝ) := by exact_mod_cast hab i
    have hb2 : (2:ℝ)≤(b i:ℝ) := by
      have h : 2≤b i := by have := ha i; have := hab i; omega
      exact_mod_cast h
    have he : 1+(a i:ℝ)/(b i:ℝ)=((b i:ℝ)+(a i:ℝ))/(b i:ℝ) := by
      rw [add_div,div_self hb0.ne']
    rw [he]
    apply (div_lt_iff₀ hb0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2) hb0.le]
  have hlt : (∏i,(1+(a i:ℝ)/(b i:ℝ))) < ∏i,(b i:ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      have ha0 : 0<(a i:ℝ) := by exact_mod_cast ha i
      have hb0 : 0<(b i:ℝ) := by exact_mod_cast hb i
      exact add_pos zero_lt_one (div_pos ha0 hb0)
    · intro i _
      exact hfactor i
    · exact Finset.univ_nonempty
  have hle' : (∏i,(b i:ℝ))≤(n:ℝ) := by exact_mod_cast hle
  rw [←hrow] at hlt
  exact (not_lt_of_ge hle') hlt

end PlanarHom.IntegerTensorObstruction
