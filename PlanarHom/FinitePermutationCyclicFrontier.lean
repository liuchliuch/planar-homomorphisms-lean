import PlanarHom.FiniteCycleSublistCuts
import PlanarHom.FinitePermutationCycleWords
import PlanarHom.FinitePermutationBoundaryPathWord

/-! NEW exact cyclic frontier-word update for a genuine boundary-path splice.
The empty retained prefix/suffix/output cases use the same literal sublists. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A B:Type} [Fintype A] [Fintype B]

 def CyclicSublist (P:Equiv.Perm A) (xs:List A) : Prop := ∃a,xs.Sublist (cycleWord P a)

 theorem cycleWord_rotate (P:Equiv.Perm A) (a:A) (k:ℕ) :
    cycleWord P (P^[k] a)=(cycleWord P a).rotate k := by
  unfold cycleWord
  rw [Function.minimalPeriod_apply_iterate (P.injective.mem_periodicPts a)]
  exact orbitPrefix_cycle_rotate P a k

 theorem CyclicSublist.sublist {P:Equiv.Perm A} {xs ys:List A}
    (h:CyclicSublist P ys) (hs:xs.Sublist ys) : CyclicSublist P xs := by
  obtain ⟨a,ha⟩:=h
  exact ⟨a,hs.trans ha⟩

 theorem CyclicSublist.append_rotate {P:Equiv.Perm A} {xs ys:List A}
    (h:CyclicSublist P (xs++ys)) : CyclicSublist P (ys++xs) := by
  by_cases hy:ys=[]
  · simpa only [hy,List.append_nil,List.nil_append] using h
  obtain ⟨a,ha⟩:=h
  have hs:=FiniteCycleSublistCuts.rotate_input_head (pre:=xs) (inputs:=ys) (post:=[])
    (cycleWord_nodup P a) hy (by simpa only [List.append_nil] using ha)
  refine ⟨P^[(cycleWord P a).idxOf (ys.head hy)] a,?_⟩
  rw [cycleWord_rotate]
  simpa only [List.append_nil] using hs

 theorem CyclicSublist.append_comm {P:Equiv.Perm A} {xs ys:List A} :
    CyclicSublist P (xs++ys) ↔ CyclicSublist P (ys++xs) :=
  ⟨CyclicSublist.append_rotate,CyclicSublist.append_rotate⟩

 theorem CyclicSublist.rotate {P:Equiv.Perm A} {xs:List A} (h:CyclicSublist P xs) (k:ℕ) :
    CyclicSublist P (xs.rotate k) := by
  rw [List.rotate_eq_drop_append_take_mod]
  exact CyclicSublist.append_rotate (by simpa only [List.take_append_drop] using h)

 theorem boundaryPathSplice_cyclic_frontier (P:Equiv.Perm A) (Q:Equiv.Perm B)
    (x:ℕ→A) (y:ℕ→B) (n l r:ℕ)
    (hxi:∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi:∀i<n+1,∀j<n+1,y i=y j→i=j)
    (hl:P^[l] (P (x n))=x 0) (hr:Q^[r] (Q (y 0))=y n)
    (hal:∀i<l,∀j<n+1,P^[i] (P (x n))≠x j)
    (har:∀i<r,∀j<n+1,Q^[i] (Q (y 0))≠y j)
    (pre post:List A) (outs:List B)
    (hleft:(post++pre).Sublist (orbitPrefix P l (P (x n))))
    (hright:outs.Sublist (orbitPrefix Q r (Q (y 0)))) :
    CyclicSublist (boundaryPathSplice P Q x y (n+1))
      (pre.map Sum.inl++outs.map Sum.inr++post.map Sum.inl) := by
  have he:= (boundaryPathSplice_exterior P Q x y n l r hxi hyi hl hr hal har).2
  have hs:CyclicSublist (boundaryPathSplice P Q x y (n+1))
      ((outs.map Sum.inr++post.map Sum.inl)++pre.map Sum.inl):=by
    refine ⟨.inl (x 0),?_⟩
    change List.Sublist _ (orbitPrefix _ _ _)
    rw [he]
    have hh:=((hright.map Sum.inr).append ((hleft.map Sum.inl).cons (.inr (y n)))).cons (.inl (x 0))
    simpa only [List.map_append,List.singleton_append,List.append_assoc,List.cons_append] using hh
  simpa only [List.append_assoc] using hs.append_rotate

end PlanarHom.FinitePermutationCycles
