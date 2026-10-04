import PlanarHom.PlanarityLRTreeCuts
import PlanarHom.FinitePermutationCut

/-! NEW exact cycle structure of the computed tree contour. Selected tree
occurrences have two sides in one contour cycle by the unique-subtree-cut proof. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

def typedOutward (g : MixedCode) (e : Fin g.edges.length) : Dart (Fin g.edges.length) :=
  liftDart (PlanarityRotationCode.outward g e.val) e.isLt

@[simp] theorem erase_typedOutward (g : MixedCode) (e : Fin g.edges.length) :
    eraseDart (typedOutward g e) = PlanarityRotationCode.outward g e.val := erase_liftDart ..
@[simp] theorem typedOutward_index (g : MixedCode) (e : Fin g.edges.length) : (typedOutward g e).1=e := rfl
@[simp] theorem dartHost_typedOutward (g : MixedCode) (e : Fin g.edges.length) :
    dartHost g (typedOutward g e) = source g e.val := by simp only [dartHost,erase_typedOutward,PlanarityRotationCode.host_outward]
@[simp] theorem dartHost_reverse_typedOutward (g : MixedCode) (e : Fin g.edges.length) :
    dartHost g (reversePerm _ (typedOutward g e)) = target g e.val := by
  simp only [dartHost,erase_reversePerm,erase_typedOutward,PlanarityRotationCode.host_reverse_outward]

 theorem exists_typedOutward (g : MixedCode) (a : Dart (Fin g.edges.length)) :
    ∃ e : Fin g.edges.length, a=typedOutward g e ∨ a=reversePerm _ (typedOutward g e) := by
  refine ⟨a.1,?_⟩
  rcases PlanarityRotationCode.dart_outward_cases g (eraseDart a) with h | h
  · exact Or.inl (eraseDart_injective g (h.trans (erase_typedOutward g a.1).symm))
  · exact Or.inr (eraseDart_injective g (by simpa only [erase_reversePerm,erase_typedOutward] using h))

def dfsContourForRows (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : RotationRows (g.toMultiGraph hg)) :
    Equiv.Perm (Dart (Fin g.edges.length)) :=
  contourPermutation rows (fun e => isTree g e.val)

 theorem rotationRows_dartHost (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    dartHost g (rows.rotation a)=dartHost g a := by
  simp only [dartHost,eraseDart_host g hg]
  exact congrArg Fin.val (rows.rotation_host a)

 theorem dfsContourForRows_host_tree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) (ha : isTree g a.1.val=true) :
    dartHost g (dfsContourForRows g hg rows a)=dartHost g (reversePerm _ a) := by
  rw [dfsContourForRows,contourPermutation_selected _ _ a ha,rotationRows_dartHost]

 theorem dfsContourForRows_host_port (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) (ha : isTree g a.1.val=false) :
    dartHost g (dfsContourForRows g hg rows a)=dartHost g a := by
  rw [dfsContourForRows,contourPermutation_port _ _ a ha,rotationRows_dartHost]

/-- Both sides of every computed tree edge lie in the same actual contour cycle.
The proof uses its unique subtree cut, not a genus or embedding premise. -/
theorem dfsContourForRows_tree_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    (dfsContourForRows g hg rows).SameCycle (typedOutward g e) (reversePerm _ (typedOutward g e)) := by
  let q := fun a : Dart (Fin g.edges.length) => Desc g (target g e.val) (dartHost g a)
  apply FinitePermutationCut.sameCycle_of_unique_exit (dfsContourForRows g hg rows) q
  · change Desc g (target g e.val) (dartHost g (dfsContourForRows g hg rows (typedOutward g e)))
    rw [dfsContourForRows_host_tree g hg rows _ he,dartHost_reverse_typedOutward]
    exact Or.inl rfl
  · change ¬Desc g (target g e.val) (dartHost g (typedOutward g e))
    rw [dartHost_typedOutward]
    exact tree_child_not_desc_source g hg he
  · intro a hin hout
    change Desc g (target g e.val) (dartHost g a) at hin
    change ¬Desc g (target g e.val) (dartHost g (dfsContourForRows g hg rows a)) at hout
    by_cases ha : isTree g a.1.val=true
    · rw [dfsContourForRows_host_tree g hg rows a ha] at hout
      obtain ⟨f,ha' | ha'⟩ := exists_typedOutward g a
      · subst a
        simp only [typedOutward_index] at ha
        rw [dartHost_typedOutward] at hin
        rw [dartHost_reverse_typedOutward] at hout
        exact False.elim (hout (tree_subtree_forward g hg ha hin))
      · subst a
        change isTree g f.val=true at ha
        rw [dartHost_reverse_typedOutward] at hin
        have hrev : reversePerm _ (reversePerm _ (typedOutward g f))=typedOutward g f := by exact (reversePerm _).symm_apply_apply _
        rw [hrev,dartHost_typedOutward] at hout
        have hfe : f=e := Fin.ext (tree_subtree_unique_entry g hg he ha hin hout)
        rw [hfe]
    · rw [dfsContourForRows_host_port g hg rows a (Bool.eq_false_iff.mpr ha)] at hout
      exact False.elim (hout hin)

 theorem dfsContourForRows_sameCycle_reverse (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) (ha : isTree g a.1.val=true) :
    (dfsContourForRows g hg rows).SameCycle a (reversePerm _ a) := by
  obtain ⟨e,rfl | rfl⟩ := exists_typedOutward g a
  · exact dfsContourForRows_tree_sameCycle g hg rows e ha
  · have h := (dfsContourForRows_tree_sameCycle g hg rows e ha).symm
    have heq : reversePerm _ (reversePerm _ (typedOutward g e))=typedOutward g e :=
      (reversePerm _).symm_apply_apply _
    rw [heq]
    exact h

 theorem dfsContourForRows_sameCycle_rotation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    (dfsContourForRows g hg rows).SameCycle a (rows.rotation a) := by
  by_cases ha : isTree g a.1.val=true
  · have h := (dfsContourForRows_sameCycle_reverse g hg rows a ha).apply_right
    have heq : dfsContourForRows g hg rows (reversePerm _ a)=rows.rotation a := by
      rw [dfsContourForRows,contourPermutation_selected _ _ (reversePerm _ a) ha]
      exact congrArg _ ((reversePerm _).symm_apply_apply a)
    rw [heq] at h
    exact h
  · have h : (dfsContourForRows g hg rows).SameCycle a (dfsContourForRows g hg rows a) := Equiv.Perm.sameCycle_apply_right.mpr .rfl
    rw [dfsContourForRows,contourPermutation_port _ _ a (Bool.eq_false_iff.mpr ha)] at h
    exact h

 theorem dfsContourForRows_sameCycle_of_sameHost (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (Fin g.edges.length)) (hab : dartHost g a=dartHost g b) :
    (dfsContourForRows g hg rows).SameCycle a b := by
  have hhost : ((g.toMultiGraph hg).dartPair a).1=((g.toMultiGraph hg).dartPair b).1 := by
    apply Fin.ext
    simpa only [dartHost,eraseDart_host g hg] using hab
  obtain ⟨n,hn⟩ := rows.exists_rotation_iterate_of_sameHost a b hhost
  suffices ∀ n, (dfsContourForRows g hg rows).SameCycle a (rows.rotation^[n] a) by
    simpa only [hn] using this n
  intro n
  induction n with
  | zero => exact .rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (dfsContourForRows_sameCycle_rotation g hg rows _)

 theorem dfsContourForRows_to_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    ∃ b : Dart (Fin g.edges.length), dartHost g b=componentRoot g (dartHost g a) ∧
      (dfsContourForRows g hg rows).SameCycle a b := by
  suffices ∀ n (a : Dart (Fin g.edges.length)), height g (dartHost g a)=n →
      ∃ b : Dart (Fin g.edges.length), dartHost g b=componentRoot g (dartHost g a) ∧
        (dfsContourForRows g hg rows).SameCycle a b from this _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a hn
      have hv := dartHost_valid g hg a
      by_cases hz : height g (dartHost g a)=0
      · exact ⟨a,(componentRoot_eq_self g hv hz).symm,.rfl⟩
      · have hpos := Nat.pos_of_ne_zero hz
        have hp := parentEdge_tree g hg hv hpos
        let e : Fin g.edges.length := ⟨parentEdge g (dartHost g a),(of_decide_eq_true hp.1).1⟩
        let p := typedOutward g e
        have hph : dartHost g p=parentVertex g (dartHost g a) := (dartHost_typedOutward g e).trans hp.2.2
        have hrh : dartHost g (reversePerm _ p)=dartHost g a := (dartHost_reverse_typedOutward g e).trans hp.2.1
        have hlt : height g (dartHost g p)<n := by rw [hph,← hn]; exact parentVertex_height_lt g hv hpos
        obtain ⟨b,hb,hr⟩ := ih _ hlt p rfl
        refine ⟨b,?_,?_⟩
        · rw [hb,hph]
          exact componentRoot_eq_of_desc g hv (Or.inr (parentVertex_ancestor g hv hpos))
        · exact (dfsContourForRows_sameCycle_of_sameHost g hg rows a (reversePerm _ p) hrh.symm).trans
            ((dfsContourForRows_tree_sameCycle g hg rows e hp.1).symm.trans hr)

 theorem dfsContourForRows_sameCycle_of_componentRoot_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (Fin g.edges.length))
    (hroot : componentRoot g (dartHost g a)=componentRoot g (dartHost g b)) :
    (dfsContourForRows g hg rows).SameCycle a b := by
  obtain ⟨a',ha',haa'⟩ := dfsContourForRows_to_componentRoot g hg rows a
  obtain ⟨b',hb',hbb'⟩ := dfsContourForRows_to_componentRoot g hg rows b
  exact haa'.trans ((dfsContourForRows_sameCycle_of_sameHost g hg rows a' b'
    (ha'.trans (hroot.trans hb'.symm))).trans hbb'.symm)

 theorem dfsContourForRows_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    componentRoot g (dartHost g (dfsContourForRows g hg rows a))=componentRoot g (dartHost g a) := by
  by_cases ht : isTree g a.1.val=true
  · rw [dfsContourForRows_host_tree g hg rows a ht]
    exact reverse_componentRoot g hg (a := eraseDart a) a.1.isLt
  · rw [dfsContourForRows_host_port g hg rows a (Bool.eq_false_iff.mpr ht)]

 theorem dfsContourForRows_sameCycle_iff_componentRoot_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (Fin g.edges.length)) :
    (dfsContourForRows g hg rows).SameCycle a b ↔ componentRoot g (dartHost g a)=componentRoot g (dartHost g b) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hall : ∀ n, componentRoot g (dartHost g ((dfsContourForRows g hg rows)^[n] a))=componentRoot g (dartHost g a) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',dfsContourForRows_componentRoot,ih]
    have hh := hall n
    rw [Equiv.Perm.iterate_eq_pow,hn] at hh
    exact hh.symm
  · exact dfsContourForRows_sameCycle_of_componentRoot_eq g hg rows a b

/-- The actual emitted contour word contains exactly all non-tree ports in the
computed component, each once. -/
theorem mem_dfsContourForRowsPortWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (Fin g.edges.length)) :
    b ∈ contourPortWord rows (fun e => isTree g e.val) a ↔
      componentRoot g (dartHost g a)=componentRoot g (dartHost g b) ∧ isTree g b.1.val=false := by
  rw [mem_contourPortWord_iff]
  change (dfsContourForRows g hg rows).SameCycle a b ∧ _ ↔ _
  rw [dfsContourForRows_sameCycle_iff_componentRoot_eq g hg rows a b]

/-- Specialize the general contour to the literal computed LR rows. -/
abbrev dfsContour (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    Equiv.Perm (Dart (Fin g.edges.length)) := dfsContourForRows g hg (directRotationRows g hg bits)

theorem dfsContour_sameCycle_iff_componentRoot_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length)) :
    (dfsContour g hg bits).SameCycle a b ↔ componentRoot g (dartHost g a)=componentRoot g (dartHost g b) :=
  dfsContourForRows_sameCycle_iff_componentRoot_eq g hg (directRotationRows g hg bits) a b

theorem mem_dfsContourPortWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length)) :
    b ∈ contourPortWord (directRotationRows g hg bits) (fun e => isTree g e.val) a ↔
      componentRoot g (dartHost g a)=componentRoot g (dartHost g b) ∧ isTree g b.1.val=false :=
  mem_dfsContourForRowsPortWord g hg (directRotationRows g hg bits) a b

end PlanarHom.PlanarityLRRealization
