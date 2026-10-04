import PlanarHom.PlanarityLRContourCycles
import PlanarHom.FinitePermutationCutInterval

/-! NEW exact subtree interval in the actual selected-tree contour cycle. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 theorem dfsContourForRows_unique_exit (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (a : Dart (Fin g.edges.length)) (hin : Desc g (target g e.val) (dartHost g a))
    (hout : ¬Desc g (target g e.val) (dartHost g (dfsContourForRows g hg rows a))) :
    a=reversePerm _ (typedOutward g e) := by
  by_cases ha : isTree g a.1.val=true
  · rw [dfsContourForRows_host_tree g hg rows a ha] at hout
    obtain ⟨f,rfl | rfl⟩ := exists_typedOutward g a
    · change isTree g f.val=true at ha
      rw [dartHost_typedOutward] at hin
      rw [dartHost_reverse_typedOutward] at hout
      exact False.elim (hout (tree_subtree_forward g hg ha hin))
    · change isTree g f.val=true at ha
      rw [dartHost_reverse_typedOutward] at hin
      have hrev : reversePerm _ (reversePerm _ (typedOutward g f))=typedOutward g f :=
        (reversePerm _).symm_apply_apply _
      rw [hrev,dartHost_typedOutward] at hout
      have hfe : f=e := Fin.ext (tree_subtree_unique_entry g hg he ha hin hout)
      rw [hfe]
  · rw [dfsContourForRows_host_port g hg rows a (Bool.eq_false_iff.mpr ha)] at hout
    exact False.elim (hout hin)

 theorem dfsContourForRows_unique_entry (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (a : Dart (Fin g.edges.length)) (hout : ¬Desc g (target g e.val) (dartHost g a))
    (hin : Desc g (target g e.val) (dartHost g (dfsContourForRows g hg rows a))) :
    a=typedOutward g e := by
  by_cases ha : isTree g a.1.val=true
  · rw [dfsContourForRows_host_tree g hg rows a ha] at hin
    obtain ⟨f,rfl | rfl⟩ := exists_typedOutward g a
    · change isTree g f.val=true at ha
      rw [dartHost_typedOutward] at hout
      rw [dartHost_reverse_typedOutward] at hin
      have hfe : f=e := Fin.ext (tree_subtree_unique_entry g hg he ha hin hout)
      rw [hfe]
    · change isTree g f.val=true at ha
      rw [dartHost_reverse_typedOutward] at hout
      have hrev : reversePerm _ (reversePerm _ (typedOutward g f))=typedOutward g f :=
        (reversePerm _).symm_apply_apply _
      rw [hrev,dartHost_typedOutward] at hin
      exact False.elim (hout (tree_subtree_forward g hg ha hin))
  · rw [dfsContourForRows_host_port g hg rows a (Bool.eq_false_iff.mpr ha)] at hin
    exact False.elim (hout hin)

/-- After the outward tree dart, exactly the descendant-host darts are visited,
ending with the reverse tree dart, before the contour returns to other hosts. -/
theorem dfsContourForRows_subtree_interval (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (k : ℕ) (hk : k  <  Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e))
    (hbk : (dfsContourForRows g hg rows)^[k] (typedOutward g e)=reversePerm _ (typedOutward g e))
    (i : ℕ) (hi : i  <  Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e)) :
    Desc g (target g e.val) (dartHost g ((dfsContourForRows g hg rows)^[i] (typedOutward g e))) ↔
      0 < i ∧ i≤k := by
  apply FinitePermutationCut.iterate_cut_interval (dfsContourForRows g hg rows)
    (fun a => Desc g (target g e.val) (dartHost g a)) (typedOutward g e)
    (reversePerm _ (typedOutward g e)) _ _ _ _ _ k hk hbk i hi
  all_goals dsimp only
  · rw [dartHost_typedOutward]
    exact tree_child_not_desc_source g hg he
  · rw [dfsContourForRows_host_tree g hg rows _ he,dartHost_reverse_typedOutward]
    exact Or.inl rfl
  · rw [dfsContourForRows_host_tree g hg rows (reversePerm _ (typedOutward g e)) he]
    have hrev : reversePerm _ (reversePerm _ (typedOutward g e))=typedOutward g e :=
      (reversePerm _).symm_apply_apply _
    rw [hrev,dartHost_typedOutward]
    exact tree_child_not_desc_source g hg he
  · exact dfsContourForRows_unique_entry g hg rows e he
  · exact dfsContourForRows_unique_exit g hg rows e he

/-- The exit index and full interval law are derived, not supplied. -/
theorem dfsContourForRows_subtree_interval_exists (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    ∃ k, 0 < k ∧ k  <  Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e) ∧
      (dfsContourForRows g hg rows)^[k] (typedOutward g e)=reversePerm _ (typedOutward g e) ∧
      ∀ i, i  <  Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e) →
        (Desc g (target g e.val) (dartHost g ((dfsContourForRows g hg rows)^[i] (typedOutward g e))) ↔ 0 < i ∧ i≤k) := by
  let P := dfsContourForRows g hg rows
  let a := typedOutward g e
  let p := Function.minimalPeriod P a
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
  obtain ⟨n,hn⟩ := (dfsContourForRows_tree_sameCycle g hg rows e he).exists_nat_pow_eq
  have hk : n%p < p := Nat.mod_lt _ hp
  have hbk : P^[n%p] a=reversePerm _ a := by
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
    exact hn
  have hpos : 0 < n%p := by
    by_contra hh
    have hz : n%p=0 := by omega
    rw [hz,Function.iterate_zero_apply] at hbk
    have hhost := congrArg (dartHost g) hbk
    have hne := tree_child_not_desc_source g hg he
    have heq : source g e.val=target g e.val := by
      simpa only [a,dartHost_typedOutward,dartHost_reverse_typedOutward] using hhost
    exact hne (Or.inl heq.symm)
  refine ⟨n%p,hpos,hk,hbk,?_⟩
  exact dfsContourForRows_subtree_interval g hg rows e he (n%p) hk hbk

end PlanarHom.PlanarityLRRealization
