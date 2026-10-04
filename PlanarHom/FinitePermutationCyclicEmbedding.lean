import PlanarHom.FinitePermutationCyclicFrontier

/-! NEW transport of an actual complete cycle word through an injective
permutation embedding. Used for untouched framed macro components. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A B : Type} [Fintype A] [Fintype B]
variable (P : Equiv.Perm A) (Q : Equiv.Perm B) (f : A→B) (hf : Function.Injective f)
variable (hs : ∀a,Q (f a)=f (P a))

 include hs in
 theorem cyclicEmbedding_iterate (a : A) (n : ℕ) : Q^[n] (f a)=f (P^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,hs,Function.iterate_succ_apply']

 include hf hs in
 theorem cyclicEmbedding_period (a : A) : Function.minimalPeriod Q (f a)=Function.minimalPeriod P a := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change Q^[n] (f a)=f a ↔ P^[n] a=a
  rw [cyclicEmbedding_iterate P Q f hs]
  exact hf.eq_iff

 include hf hs in
 theorem cyclicEmbedding_word (a : A) : cycleWord Q (f a)=(cycleWord P a).map f := by
  simp only [cycleWord,cyclicEmbedding_period P Q f hf hs,orbitPrefix,List.map_map,Function.comp_def,
    cyclicEmbedding_iterate P Q f hs]

 include hf hs in
 theorem CyclicSublist.map_embedding {xs : List A} (h : CyclicSublist P xs) : CyclicSublist Q (xs.map f) := by
  obtain ⟨a,ha⟩:=h
  refine ⟨f a,?_⟩
  rw [cyclicEmbedding_word P Q f hf hs]
  exact ha.map f


end PlanarHom.FinitePermutationCycles
