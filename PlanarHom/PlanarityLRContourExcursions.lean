import PlanarHom.PlanarityLRContourSubtreeIntervals
import PlanarHom.FinitePermutationCutExistence

/-! NEW exact first-return excursions from every literal host row dart. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

/-- The contour reaches the next local row dart after a nonempty excursion,
without visiting this host in between. This includes the incoming parent dart. -/
theorem contour_host_excursion (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    ∃ n, 0 < n ∧ n≤Function.minimalPeriod (dfsContourForRows g hg rows) a ∧
      (dfsContourForRows g hg rows)^[n] a=rows.rotation a ∧
      ∀ i, 0 < i → i < n → dartHost g ((dfsContourForRows g hg rows)^[i] a)≠dartHost g a := by
  let P := dfsContourForRows g hg rows
  by_cases ha : isTree g a.1.val=true
  · obtain ⟨e,rfl | rfl⟩ := exists_typedOutward g a
    · change isTree g e.val=true at ha
      obtain ⟨k,hkpos,hk,hend,hcut⟩ := dfsContourForRows_subtree_interval_exists g hg rows e ha
      refine ⟨k+1,by omega,by omega,?_,?_⟩
      · rw [Function.iterate_succ_apply',hend]
        rw [dfsContourForRows,contourPermutation_selected _ _ (reversePerm _ (typedOutward g e)) ha]
        exact congrArg rows.rotation ((reversePerm _).symm_apply_apply _)
      · intro i hip hik heq
        have hd := (hcut i (by omega)).mpr ⟨hip,by omega⟩
        rw [heq,dartHost_typedOutward] at hd
        exact tree_child_not_desc_source g hg ha hd
    · change isTree g e.val=true at ha
      let q := fun x : Dart (Fin g.edges.length) => ¬Desc g (target g e.val) (dartHost g x)
      have hstart : ¬q (reversePerm _ (typedOutward g e)) := by
        intro h
        exact h (by rw [dartHost_reverse_typedOutward]; exact Or.inl rfl)
      have hin : q (P (reversePerm _ (typedOutward g e))) := by
        change ¬Desc g (target g e.val) (dartHost g (P (reversePerm _ (typedOutward g e))))
        rw [dfsContourForRows_host_tree g hg rows _ ha]
        have heq : reversePerm _ (reversePerm _ (typedOutward g e))=typedOutward g e := (reversePerm _).symm_apply_apply _
        rw [heq,dartHost_typedOutward]
        exact tree_child_not_desc_source g hg ha
      have hb : q (typedOutward g e) := by
        change ¬Desc g (target g e.val) (dartHost g (typedOutward g e))
        rw [dartHost_typedOutward]
        exact tree_child_not_desc_source g hg ha
      have hout : ¬q (P (typedOutward g e)) := by
        intro h
        apply h
        rw [dfsContourForRows_host_tree g hg rows _ ha,dartHost_reverse_typedOutward]
        exact Or.inl rfl
      have hentry : ∀ x, ¬q x → q (P x) → x=reversePerm _ (typedOutward g e) := by
        intro x hx hy
        exact dfsContourForRows_unique_exit g hg rows e ha x (Classical.not_not.mp hx) hy
      have hexit : ∀ x, q x → ¬q (P x) → x=typedOutward g e := by
        intro x hx hy
        exact dfsContourForRows_unique_entry g hg rows e ha x hx (Classical.not_not.mp hy)
      obtain ⟨k,hkpos,hk,hend,hcut⟩ := FinitePermutationCut.exists_cut_interval P q
        (reversePerm _ (typedOutward g e)) (typedOutward g e) hstart hin hb hout hentry hexit
      change k < Function.minimalPeriod (dfsContourForRows g hg rows) _ at hk
      refine ⟨k+1,by omega,by omega,?_,?_⟩
      · rw [Function.iterate_succ_apply',hend]
        exact contourPermutation_selected rows _ (typedOutward g e) ha
      · intro i hip hik heq
        have hno := (hcut i (lt_of_lt_of_le hik (Nat.succ_le_of_lt hk))).mpr ⟨hip,by omega⟩
        apply hno
        rw [heq,dartHost_reverse_typedOutward]
        exact Or.inl rfl
  · have hport := Bool.eq_false_iff.mpr ha
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
    change 0 < Function.minimalPeriod (dfsContourForRows g hg rows) a at hp
    refine ⟨1,by omega,by omega,?_,?_⟩
    · simp only [Function.iterate_one]
      exact contourPermutation_port rows _ a hport
    · intro i hi hin
      omega

end PlanarHom.PlanarityLRRealization
