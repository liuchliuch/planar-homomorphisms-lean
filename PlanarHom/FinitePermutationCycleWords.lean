import PlanarHom.FinitePermutationReturnWords
import PlanarHom.FinitePermutationCycleProducts
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! NEW exact orbit-word/cardinality/product interface for literal face fibers. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A : Type*} [Finite A]

 def cycleWord (P : Equiv.Perm A) (a : A) : List A := orbitPrefix P (Function.minimalPeriod P a) a

 theorem cycleWord_nodup (P : Equiv.Perm A) (a : A) : (cycleWord P a).Nodup :=
  orbitPrefix_nodup P a (le_refl _)

 theorem mem_cycleWord (P : Equiv.Perm A) (a b : A) : b∈cycleWord P a ↔ P.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n,_,hn⟩ := (mem_orbitPrefix P _ _ _).mp h
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
    refine (mem_orbitPrefix P _ _ _).mpr ⟨n%Function.minimalPeriod P a,Nat.mod_lt _ hp,?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
    exact hn

 theorem cycleWord_perm_of_sameCycle (P : Equiv.Perm A) (a b : A) (hab : P.SameCycle a b) :
    (cycleWord P a).Perm (cycleWord P b) := by
  apply (List.perm_ext_iff_of_nodup (cycleWord_nodup P a) (cycleWord_nodup P b)).mpr
  intro x
  rw [mem_cycleWord,mem_cycleWord]
  exact ⟨fun h => hab.symm.trans h,fun h => hab.trans h⟩

 def cycleFiberEquiv (P : Equiv.Perm A) (a : A) :
    Fin (cycleWord P a).length ≃ {b : A // classOf P b=classOf P a} :=
  (List.Nodup.getEquiv (cycleWord P a) (cycleWord_nodup P a)).trans
    (Equiv.subtypeEquivRight (fun b =>
      ⟨fun h => Quotient.sound ((mem_cycleWord P a b).mp h).symm,
       fun h => (mem_cycleWord P a b).mpr (Quotient.exact h).symm⟩))

 theorem cycleFiber_card [Fintype A] (P : Equiv.Perm A) (a : A) :
    Fintype.card {b : A // classOf P b=classOf P a}=(cycleWord P a).length := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (cycleFiberEquiv P a)).symm

 theorem cycleFiber_product [Fintype A] {M : Type*} [CommMonoid M]
    (P : Equiv.Perm A) (a : A) (w : A → M) :
    (∏b : {b : A // classOf P b=classOf P a},w b.val)=((cycleWord P a).map w).prod := by
  rw [←(cycleFiberEquiv P a).prod_comp (fun b => w b.val)]
  have h := congrArg (fun xs : List A => (xs.map w).prod) (List.ofFn_get (cycleWord P a))
  dsimp only at h
  rw [List.map_ofFn,List.prod_ofFn] at h
  exact h

end PlanarHom.FinitePermutationCycles
