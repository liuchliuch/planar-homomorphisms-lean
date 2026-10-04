import PlanarHom.FinitePermutationCyclicFrontier

/-! NEW canonical-carrier frontier update under the actual splicePrefix.
No carrier repartition or sum-type conversion is used. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A:Type} [Fintype A]

 theorem splicePrefix_cyclic_frontier (P:Equiv.Perm A) (x y:ℕ→A) (n l r:ℕ)
    (hd:DistinctPathMarkers x y (n+1)) (hsep:¬P.SameCycle (x 0) (y 0))
    (hl:P^[l] (P (x n))=x 0) (hr:P^[r] (P (y 0))=y n)
    (hal:∀i<l,∀j<n+1,P^[i] (P (x n))≠x j ∧ P^[i] (P (x n))≠y j)
    (har:∀i<r,∀j<n+1,P^[i] (P (y 0))≠x j ∧ P^[i] (P (y 0))≠y j)
    (pre post outs:List A)
    (hleft:(post++pre).Sublist (orbitPrefix P l (P (x n))))
    (hright:outs.Sublist (orbitPrefix P r (P (y 0)))) :
    CyclicSublist (splicePrefix P x y (n+1)) (pre++outs++post) := by
  have he:=(splicePrefix_exterior_cycle P x y n l r hd hsep hl hr hal har).2
  have hs:CyclicSublist (splicePrefix P x y (n+1)) ((outs++post)++pre):=by
    refine ⟨x 0,?_⟩
    change List.Sublist _ (orbitPrefix _ _ _)
    rw [he]
    have hh:=(hright.append (hleft.cons (y n))).cons (x 0)
    simpa only [splicedExteriorWord,List.singleton_append,List.append_assoc,List.cons_append] using hh
  simpa only [List.append_assoc] using hs.append_rotate

end PlanarHom.FinitePermutationCycles
