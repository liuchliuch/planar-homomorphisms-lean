import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! NEW denominator product lemma for the integer tensor obstruction in §7.
For each prime, select exactly the denominators it divides. Coprimality prevents
cancellation by the selected numerators, so their full denominator product must
divide the original integer scalar. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.TensorDenominatorProduct
variable {I : Type} [Fintype I]

theorem product_dvd (n : ℕ) (a b : I → ℕ) (hc : ∀i,Nat.Coprime (a i) (b i))
    (hsub : ∀S : Finset I, (∏i∈S,b i) ∣ n*(∏i∈S,a i)) : (∏i,b i) ∣ n := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd n (∏i,b i)).mpr
  intro p k hp hpk
  let S : Finset I := Finset.univ.filter (fun i=>p ∣ b i)
  let T : Finset I := Finset.univ.filter (fun i=>¬p ∣ b i)
  have hsplit : (∏i∈S,b i)*(∏i∈T,b i)=∏i,b i :=
    Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>p ∣ b i) b
  have hpT : Nat.Coprime (p^k) (∏i∈T,b i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    exact (hp.coprime_pow_of_not_dvd (Finset.mem_filter.mp hi).2).symm
  have hselected : p^k ∣ ∏i∈S,b i := by
    rw [←hsplit] at hpk
    exact hpT.dvd_of_dvd_mul_right hpk
  have hpS : Nat.Coprime (p^k) (∏i∈S,a i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    apply Nat.Coprime.symm
    apply hp.coprime_pow_of_not_dvd
    intro hpa
    have hpb := (Finset.mem_filter.mp hi).2
    have hh := Nat.dvd_gcd hpa hpb
    have hcop : Nat.gcd (a i) (b i)=1 := hc i
    rw [hcop] at hh
    exact hp.ne_one (Nat.dvd_one.mp hh)
  exact hpS.dvd_of_dvd_mul_right (hselected.trans (hsub S))

end PlanarHom.TensorDenominatorProduct
