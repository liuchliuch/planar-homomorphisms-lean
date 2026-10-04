import PlanarHom.PlanarityLRSubtreeWordStart

/-! NEW exact classification of genuine first-host-return contour excursions.
All words are the existing bounded minimal-period and first-return programs. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords
local instance excursionPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem hostExcursionLength_eq_of_first_return (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length))
    (n : ℕ) (hn : 0<n)
    (hend : dartHost g ((dfsContourForRows g hg rows)^[n] a)=dartHost g a)
    (hfirst : ∀ i,0 < i→i < n→dartHost g ((dfsContourForRows g hg rows)^[i] a)≠dartHost g a) :
    hostExcursionLength g hg rows a=n := by
  have hs := hostExcursionLength_spec g hg rows a
  have he : dartHost g ((dfsContourForRows g hg rows)^[hostExcursionLength g hg rows a] a)=dartHost g a := by
    rw [hs.2.2.1]
    exact rotationRows_dartHost g hg rows a
  rcases lt_trichotomy (hostExcursionLength g hg rows a) n with h | h | h
  · exact (hfirst _ hs.1 h he).elim
  · exact h
  · exact (hs.2.2.2 n hn h hend).elim

theorem hostExcursionLength_nonTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length))
    (ha : isTree g a.1.val=false) : hostExcursionLength g hg rows a=1 := by
  apply hostExcursionLength_eq_of_first_return g hg rows a 1 (by omega)
  · rw [Function.iterate_one]
    rw [show dfsContourForRows g hg rows a=rows.rotation a from contourPermutation_port rows _ a ha]
    exact rotationRows_dartHost g hg rows a
  · intro i hi hin
    omega

theorem hostExcursionWord_nonTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length))
    (ha : isTree g a.1.val=false) :
    (hostExcursionWord g hg rows a).filter (fun b=> !(isTree g b.1.val))=[a] := by
  simp [hostExcursionWord,hostExcursionLength_nonTree g hg rows a ha,orbitPrefix,ha]

theorem hostExcursionLength_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (k : ℕ) (hkpos : 0<k) (hk : k<Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e))
    (hend : (dfsContourForRows g hg rows)^[k] (typedOutward g e)=reversePerm _ (typedOutward g e))
    (hcut : ∀ i,i<Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e)→
      (Desc g (target g e.val) (dartHost g ((dfsContourForRows g hg rows)^[i] (typedOutward g e))) ↔ 0 < i ∧ i ≤ k)) :
    hostExcursionLength g hg rows (typedOutward g e)=k+1 := by
  apply hostExcursionLength_eq_of_first_return g hg rows _ (k+1) (by omega)
  · rw [Function.iterate_succ_apply',hend]
    rw [dfsContourForRows,contourPermutation_selected _ _ (reversePerm _ (typedOutward g e)) he]
    rw [show reversePerm _ (reversePerm _ (typedOutward g e))=typedOutward g e from (reversePerm _).symm_apply_apply _]
    exact rotationRows_dartHost g hg rows _
  · intro i hip hik hh
    have hd := (hcut i (by omega)).mpr ⟨hip,by omega⟩
    rw [hh,dartHost_typedOutward] at hd
    exact tree_child_not_desc_source g hg he hd

theorem hostExcursionWord_forward_support (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (a : Dart (Fin g.edges.length))
    (ha : a∈(hostExcursionWord g hg rows (typedOutward g e)).filter (fun b=> !(isTree g b.1.val))) :
    Desc g (target g e.val) (dartHost g a) := by
  obtain ⟨k,hkpos,hk,hend,hcut⟩ := dfsContourForRows_subtree_interval_exists g hg rows e he
  have hl := hostExcursionLength_forward g hg rows e he k hkpos hk hend hcut
  obtain ⟨hm,ht⟩ := List.mem_filter.mp ha
  rw [hostExcursionWord,hl] at hm
  obtain ⟨i,hi,rfl⟩ := (mem_orbitPrefix _ _ _ _).mp hm
  have hip : 0 < i := by
    by_contra hn
    have hz : i=0 := by omega
    subst i
    change Bool.not (isTree g e.val)=true at ht
    simp [he] at ht
  exact (hcut i (by omega)).mpr ⟨hip,by omega⟩

theorem hostExcursionWord_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    (hostExcursionWord g hg rows (typedOutward g e)).filter (fun b=> !(isTree g b.1.val))=
      subtreeContourPorts g hg rows e := by
  let P := dfsContourForRows g hg rows
  let a := typedOutward g e
  let N := Function.minimalPeriod P a
  obtain ⟨k,hkpos,hk,hend,hcut⟩ := dfsContourForRows_subtree_interval_exists g hg rows e he
  have hl := hostExcursionLength_forward g hg rows e he k hkpos hk hend hcut
  have hp : (orbitPrefix P (k+1) a).filter (fun b=> !(isTree g b.1.val))=
      (orbitPrefix P (k+1) a).filter (subtreePortKeep g e) := by
    apply List.filter_congr
    intro b hb
    by_cases ht : isTree g b.1.val=true
    · simp [subtreePortKeep,ht]
    · have hf : isTree g b.1.val=false := Bool.eq_false_iff.mpr ht
      have hs := hostExcursionWord_forward_support g hg rows e he b (by
        apply List.mem_filter.mpr
        exact ⟨by simpa only [hostExcursionWord,hl] using hb,by simp [hf]⟩)
      change (target g e.val=dartHost g b ∨ target g e.val∈PlanarityDepthFirstSearch.ancestors g (dartHost g b)) at hs
      simp [subtreePortKeep,hf,hs]
  have htail : (orbitPrefix P (N-(k+1)) (P^[k+1] a)).filter (subtreePortKeep g e)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb hbkeep
    obtain ⟨i,hi,hb⟩ := (mem_orbitPrefix _ _ _ _).mp hb
    have hidx : k+1+i<N := by omega
    have heq : P^[k+1+i] a=b := by
      rw [Nat.add_comm,Function.iterate_add_apply]
      exact hb
    have hd : Desc g (target g e.val) (dartHost g b) := by
      have hdec := (Bool.and_eq_true_iff.mp hbkeep).2
      simpa only [decide_eq_true_eq] using hdec
    rw [←heq] at hd
    have := ((hcut _ hidx).mp hd).2
    omega
  change (orbitPrefix P (hostExcursionLength g hg rows a) a).filter _=(orbitPrefix P N a).filter _
  rw [hl,hp]
  have hkN : k<N := hk
  conv_rhs => rw [show N=(k+1)+(N-(k+1)) by omega,orbitPrefix_add,List.filter_append,htail,List.append_nil]

theorem hostExcursionWord_reverse (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    (hostExcursionWord g hg rows (reversePerm _ (typedOutward g e))).filter (subtreePortKeep g e)=[] := by
  let P := dfsContourForRows g hg rows
  let a := typedOutward g e
  let q := fun x : Dart (Fin g.edges.length) => ¬Desc g (target g e.val) (dartHost g x)
  have hstart : ¬q (reversePerm _ a) := by
    intro h
    exact h (by rw [dartHost_reverse_typedOutward]; exact Or.inl rfl)
  have hin : q (P (reversePerm _ a)) := by
    change ¬Desc g (target g e.val) (dartHost g (P (reversePerm _ (typedOutward g e))))
    rw [dfsContourForRows_host_tree g hg rows _ he]
    have heq : reversePerm _ (reversePerm _ (typedOutward g e))=typedOutward g e := (reversePerm _).symm_apply_apply _
    rw [heq,dartHost_typedOutward]
    exact tree_child_not_desc_source g hg he
  have hb : q a := by
    change ¬Desc g (target g e.val) (dartHost g (typedOutward g e))
    rw [dartHost_typedOutward]
    exact tree_child_not_desc_source g hg he
  have hout : ¬q (P a) := by
    intro h
    apply h
    rw [dfsContourForRows_host_tree g hg rows _ he,dartHost_reverse_typedOutward]
    exact Or.inl rfl
  have hentry : ∀ x, ¬q x → q (P x) → x=reversePerm _ a := by
    intro x hx hy
    exact dfsContourForRows_unique_exit g hg rows e he x (Classical.not_not.mp hx) hy
  have hexit : ∀ x, q x → ¬q (P x) → x=a := by
    intro x hx hy
    exact dfsContourForRows_unique_entry g hg rows e he x hx (Classical.not_not.mp hy)
  obtain ⟨k,hkpos,hk,hend,hcut⟩ := FinitePermutationCut.exists_cut_interval P q
    (reversePerm _ a) a hstart hin hb hout hentry hexit
  have hl : hostExcursionLength g hg rows (reversePerm _ a)=k+1 := by
    apply hostExcursionLength_eq_of_first_return g hg rows _ (k+1) (by omega)
    · rw [Function.iterate_succ_apply',hend]
      rw [show dfsContourForRows g hg rows a=rows.rotation (reversePerm _ a) from
        contourPermutation_selected rows _ a he]
      exact rotationRows_dartHost g hg rows _
    · intro i hip hik hh
      have hno := (hcut i (by omega)).mpr ⟨hip,by omega⟩
      apply hno
      rw [hh,dartHost_reverse_typedOutward]
      exact Or.inl rfl
  apply List.filter_eq_nil_iff.mpr
  intro b hb hbkeep
  change b∈orbitPrefix P (hostExcursionLength g hg rows (reversePerm _ a)) (reversePerm _ a) at hb
  rw [hl] at hb
  obtain ⟨i,hi,rfl⟩ := (mem_orbitPrefix _ _ _ _).mp hb
  by_cases hz : i=0
  · subst i
    have hf := (Bool.and_eq_true_iff.mp hbkeep).1
    change Bool.not (isTree g e.val)=true at hf
    simp [he] at hf
  · have hno := (hcut i (by omega)).mpr ⟨by omega,by omega⟩
    apply hno
    have hdec := (Bool.and_eq_true_iff.mp hbkeep).2
    simpa only [decide_eq_true_eq] using hdec

end PlanarHom.PlanarityLRRealization
