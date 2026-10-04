import PlanarHom.PlanarityLRDirect

/-! NEW literal incidence and uniqueness of the deterministic LR rows. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode

theorem reversedOutward_injective (g : MixedCode) :
    Function.Injective (fun e => reverse (outward g e)) := by
  intro e f h
  exact congrArg Prod.fst h

theorem outward_ne_reversed (g : MixedCode) (e f : ℕ) : outward g e ≠ reverse (outward g f) := by
  intro h
  have he : e = f := congrArg Prod.fst h
  subst f
  exact reverse_ne (outward g e) h.symm

theorem source_ne_target_iff (g : MixedCode) (e : ℕ) :
    source g e ≠ target g e ↔ (edge g e).1 ≠ (edge g e).2.1 := by
  rcases source_target_endpoints g e with h | h
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only [Prod.fst,Prod.snd] at hs ht
    rw [hs,ht]
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only [Prod.fst,Prod.snd] at hs ht
    rw [hs,ht]
    exact ne_comm

theorem tree_nonloop (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) {e : ℕ} (he : isTree g e = true) :
    (edge g e).1 ≠ (edge g e).2.1 := by
  apply (source_ne_target_iff g e).mp
  intro h
  have hh := tree_height_succ g hg he
  rw [h] at hh
  omega

theorem back_nonloop (g : MixedCode) {e : ℕ} (he : isBack g e = true) :
    (edge g e).1 ≠ (edge g e).2.1 :=
  (source_ne_target_iff g e).mp (of_decide_eq_true he).2.2

theorem incoming_index (g : MixedCode) (bits : List Bool) {e : ℕ} {side : Bool} {a : Dart}
    (ha : a ∈ incoming g bits e side) :
    isBack g a.1 = true ∧ branchEdge g a.1 = e ∧ bitSide bits a.1 = side ∧ a = reverse (outward g a.1) := by
  obtain ⟨b,hb,he,hs,rfl⟩ := (mem_incoming g bits e side a).mp ha
  exact ⟨hb,he,hs,rfl⟩

theorem incoming_nodup (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) :
    (incoming g bits e side).Nodup :=
  by
    have hn : (((backEvents g bits).filter
        (fun b => decide (branchEdge g b = e ∧ bitSide bits b = side))).reverse).Nodup := by
      rw [List.nodup_reverse]
      exact (backEvents_nodup g bits).filter _
    exact hn.map (reversedOutward_injective g)

theorem incoming_out_ne (g : MixedCode) (bits : List Bool) {e : ℕ} {side : Bool} {a : Dart}
    (ha : a ∈ incoming g bits e side) (f : ℕ) : a ≠ outward g f := by
  have hh := (incoming_index g bits ha).2.2.2
  rw [hh]
  exact (outward_ne_reversed g f a.1).symm

theorem incoming_intersection (g : MixedCode) (bits : List Bool) {e f : ℕ} {s t : Bool} {a : Dart}
    (ha : a ∈ incoming g bits e s) (hb : a ∈ incoming g bits f t) : e = f ∧ s = t := by
  have h₁ := incoming_index g bits ha
  have h₂ := incoming_index g bits hb
  exact ⟨h₁.2.1.symm.trans h₂.2.1,h₁.2.2.1.symm.trans h₂.2.2.1⟩

theorem edgeBlock_nodup (g : MixedCode) (bits : List Bool) (e : ℕ) : (edgeBlock g bits e).Nodup := by
  unfold edgeBlock
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨incoming_nodup g bits e false,by simp,?_⟩,
    incoming_nodup g bits e true,?_⟩
  · intro a ha b hb
    have hb' : b = outward g e := by simpa using hb
    subst b
    exact incoming_out_ne g bits ha e
  · intro a ha b hb h
    subst b
    rcases List.mem_append.mp ha with ha | ha
    · have hh := (incoming_intersection g bits ha hb).2
      contradiction
    · have ha' : a = outward g e := by simpa using ha
      subst a
      exact incoming_out_ne g bits hb e rfl

theorem edgeBlocks_disjoint (g : MixedCode) (bits : List Bool) {e f : ℕ} (hne : e ≠ f) :
    List.Disjoint (edgeBlock g bits e) (edgeBlock g bits f) := by
  apply List.disjoint_left.mpr
  intro a ha hb
  simp only [edgeBlock,List.mem_append,List.mem_singleton] at ha hb
  rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb
  · exact hne (incoming_intersection g bits ha hb).1
  · subst a; exact incoming_out_ne g bits ha f rfl
  · exact hne (incoming_intersection g bits ha hb).1
  · subst a; exact incoming_out_ne g bits hb e rfl
  · exact hne (outward_injective g (ha.symm.trans hb))
  · subst a; exact incoming_out_ne g bits hb e rfl
  · exact hne (incoming_intersection g bits ha hb).1
  · subst a; exact incoming_out_ne g bits ha f rfl
  · exact hne (incoming_intersection g bits ha hb).1

def outgoingBlocks (g : MixedCode) (bits : List Bool) (v : ℕ) : List Dart :=
  (orderedOutgoing g bits v).flatMap (edgeBlock g bits)

theorem outgoingBlocks_nodup (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (outgoingBlocks g bits v).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun e _ => edgeBlock_nodup g bits e,?_⟩
  have h := orderedOutgoing_nodup g bits v
  change (orderedOutgoing g bits v).Pairwise (· ≠ ·) at h
  exact h.imp (fun hne => edgeBlocks_disjoint g bits hne)

@[simp] theorem mem_loopRow (g : MixedCode) (v : ℕ) (a : Dart) : a ∈ loopRow g v ↔
    a.1 < g.edges.length ∧ (edge g a.1).1 = (edge g a.1).2.1 ∧ host g a = v := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [loopRow,host] <;> aesop

theorem loopRow_nodup (g : MixedCode) (v : ℕ) : (loopRow g v).Nodup := by
  unfold loopRow
  apply List.nodup_flatMap.mpr
  refine ⟨fun _ _ => by simp,?_⟩
  have h := (List.nodup_range (n := g.edges.length)).filter
    (fun e => decide ((edge g e).1 = (edge g e).2.1 ∧ (edge g e).1 = v))
  change List.Pairwise (· ≠ ·) _ at h
  apply h.imp
  intro e f hne
  simp [List.disjoint_left,hne,Ne.symm hne]

theorem edgeBlock_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (he : e ∈ outgoing g v) {a : Dart} (ha : a ∈ edgeBlock g bits e) :
    a.1 < g.edges.length ∧ host g a = v := by
  have hs := outgoing_spec g he
  have hin (side : Bool) (h : a ∈ incoming g bits e side) : a.1 < g.edges.length ∧ host g a = v := by
    have H := incoming_index g bits h
    have HB := branchEdge_spec g hg H.1
    rw [H.2.1] at HB
    refine ⟨(of_decide_eq_true H.1).1,?_⟩
    rw [H.2.2.2,host_reverse_outward,← HB.2.1,hs.2.2]
  simp only [edgeBlock,List.mem_append,List.mem_singleton] at ha
  rcases ha with (ha | rfl) | ha
  · exact hin false ha
  · exact ⟨hs.1,by simpa using hs.2.2⟩
  · exact hin true ha

theorem outgoingBlocks_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} {a : Dart} (ha : a ∈ outgoingBlocks g bits v) :
    a.1 < g.edges.length ∧ host g a = v := by
  obtain ⟨e,he,ha⟩ := List.mem_flatMap.mp ha
  exact edgeBlock_host g hg bits ((mem_orderedOutgoing g bits v e).mp he) ha



theorem edgeBlock_nonloop (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (he : e ∈ outgoing g v) {a : Dart} (ha : a ∈ edgeBlock g bits e) :
    (edge g a.1).1 ≠ (edge g a.1).2.1 := by
  simp only [edgeBlock,List.mem_append,List.mem_singleton] at ha
  rcases ha with (ha | rfl) | ha
  · exact back_nonloop g (incoming_index g bits ha).1
  · rcases (outgoing_spec g he).2.1 with h | h
    · exact tree_nonloop g hg h
    · exact back_nonloop g h
  · exact back_nonloop g (incoming_index g bits ha).1

theorem parentRow_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) {v : ℕ}
    (hv : v < g.vertices) {a : Dart} (ha : a ∈ parentRow g v) :
    a = reverse (outward g (parentEdge g v)) ∧ isTree g a.1 = true ∧
      a.1 < g.edges.length ∧ host g a = v := by
  unfold parentRow at ha
  split_ifs at ha with hh
  · simp at ha
  · have heq : a = reverse (outward g (parentEdge g v)) := by simpa using ha
    subst a
    have hp := parentEdge_tree g hg hv (Nat.pos_of_ne_zero hh)
    exact ⟨rfl,hp.1,(of_decide_eq_true hp.1).1,by simpa using hp.2.1⟩

theorem parentRow_nodup (g : MixedCode) (v : ℕ) : (parentRow g v).Nodup := by
  unfold parentRow
  split_ifs <;> simp

theorem parent_blocks_disjoint (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v < g.vertices) :
    List.Disjoint (parentRow g v) (outgoingBlocks g bits v) := by
  apply List.disjoint_left.mpr
  intro a ha hb
  have hp := parentRow_spec g hg hv ha
  obtain ⟨e,he,hb⟩ := List.mem_flatMap.mp hb
  simp only [edgeBlock,List.mem_append,List.mem_singleton] at hb
  rcases hb with (hb | hb) | hb
  · have hh := (of_decide_eq_true (incoming_index g bits hb).1).2.1
    rw [hp.2.1] at hh
    contradiction
  · rw [hp.1] at hb
    exact (outward_ne_reversed g e (parentEdge g v)) hb.symm
  · have hh := (of_decide_eq_true (incoming_index g bits hb).1).2.1
    rw [hp.2.1] at hh
    contradiction

theorem parent_loop_disjoint (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v : ℕ} (hv : v < g.vertices) : List.Disjoint (parentRow g v) (loopRow g v) := by
  apply List.disjoint_left.mpr
  intro a ha hb
  exact tree_nonloop g hg (parentRow_spec g hg hv ha).2.1 ((mem_loopRow g v a).mp hb).2.1

theorem blocks_loop_disjoint (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : ℕ) : List.Disjoint (outgoingBlocks g bits v) (loopRow g v) := by
  apply List.disjoint_left.mpr
  intro a ha hb
  obtain ⟨e,he,ha⟩ := List.mem_flatMap.mp ha
  exact edgeBlock_nonloop g hg bits ((mem_orderedOutgoing g bits v e).mp he) ha
    ((mem_loopRow g v a).mp hb).2.1

/-- Every original occurrence dart appears at most once in its literal computed row. -/
theorem directRow_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v < g.vertices) : (directRow g bits v).Nodup := by
  change ((parentRow g v ++ outgoingBlocks g bits v) ++ loopRow g v).Nodup
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨parentRow_nodup g v,outgoingBlocks_nodup g bits v,?_⟩,
    loopRow_nodup g v,?_⟩
  · intro a ha b hb heq
    subst b
    exact (List.disjoint_left.mp (parent_blocks_disjoint g hg bits hv)) ha hb
  · intro a ha b hb heq
    subst b
    rcases List.mem_append.mp ha with ha | ha
    · exact (List.disjoint_left.mp (parent_loop_disjoint g hg hv)) ha hb
    · exact (List.disjoint_left.mp (blocks_loop_disjoint g hg bits v)) ha hb

theorem outward_mem_blocks (g : MixedCode) (bits : List Bool) {v e : ℕ} (he : e ∈ outgoing g v) :
    outward g e ∈ outgoingBlocks g bits v := by
  apply List.mem_flatMap.mpr
  exact ⟨e,(mem_orderedOutgoing g bits v e).mpr he,by simp [edgeBlock]⟩

theorem tree_backward_mem_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e v : ℕ} (he : isTree g e = true) (hv : target g e = v) :
    reverse (outward g e) ∈ parentRow g v := by
  have hp := tree_source_parent g hg he
  rw [hv] at hp
  simp only [parentRow,if_neg (Nat.ne_of_gt hp.2.2),List.mem_singleton]
  rw [hp.2.1]

theorem back_backward_mem_blocks (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e v : ℕ} (he : isBack g e = true) (hv : target g e = v) :
    reverse (outward g e) ∈ outgoingBlocks g bits v := by
  have hp := branchEdge_spec g hg he
  have hi := (of_decide_eq_true hp.1).1
  have hs : source g (branchEdge g e) = v := hp.2.1.trans hv
  have hout : branchEdge g e ∈ outgoing g v := by simp [outgoing,hi,hp.1,hs]
  apply List.mem_flatMap.mpr
  refine ⟨branchEdge g e,(mem_orderedOutgoing g bits v _).mpr hout,?_⟩
  have hin : reverse (outward g e) ∈ incoming g bits (branchEdge g e) (bitSide bits e) :=
    (mem_incoming g bits _ _ _).mpr ⟨e,he,rfl,rfl,rfl⟩
  cases hh : bitSide bits e
  · rw [hh] at hin
    simp only [edgeBlock,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl hin)
  · rw [hh] at hin
    simp only [edgeBlock,List.mem_append,List.mem_singleton]
    exact Or.inr hin

/-- The computed row consists of exactly all darts hosted at that original vertex. -/
theorem mem_directRow (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v < g.vertices) (a : Dart) :
    a ∈ directRow g bits v ↔ a.1 < g.edges.length ∧ host g a = v := by
  constructor
  · intro ha
    change a ∈ (parentRow g v ++ outgoingBlocks g bits v) ++ loopRow g v at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact (parentRow_spec g hg hv ha).2.2
      · exact outgoingBlocks_host g hg bits ha
    · have h := (mem_loopRow g v a).mp ha
      exact ⟨h.1,h.2.2⟩
  · rintro ⟨ha,hhost⟩
    change a ∈ (parentRow g v ++ outgoingBlocks g bits v) ++ loopRow g v
    by_cases hloop : (edge g a.1).1 = (edge g a.1).2.1
    · exact List.mem_append_right _ ((mem_loopRow g v a).mpr ⟨ha,hloop,hhost⟩)
    · have hne := (source_ne_target_iff g a.1).mpr hloop
      by_cases ht : isTree g a.1 = true
      · rcases dart_outward_cases g a with h | h
        · have hs : source g a.1 = v := by
            have hh := congrArg (host g) h
            rw [host_outward] at hh
            exact hh.symm.trans hhost
          have ho : a.1 ∈ outgoing g v := by simp [outgoing,ha,ht,hs]
          have hm := outward_mem_blocks g bits ho
          rw [← h] at hm
          exact List.mem_append_left _ (List.mem_append_right _ hm)
        · have hs : target g a.1 = v := by
            have hh := congrArg (host g) h
            rw [host_reverse_outward] at hh
            exact hh.symm.trans hhost
          have hm := tree_backward_mem_parent g hg ht hs
          rw [← h] at hm
          exact List.mem_append_left _ (List.mem_append_left _ hm)
      · have hf : isTree g a.1 = false := Bool.eq_false_iff.mpr ht
        have hb : isBack g a.1 = true := by simp [isBack,ha,hf,hne]
        rcases dart_outward_cases g a with h | h
        · have hs : source g a.1 = v := by
            have hh := congrArg (host g) h
            rw [host_outward] at hh
            exact hh.symm.trans hhost
          have ho : a.1 ∈ outgoing g v := by simp [outgoing,ha,hb,hs]
          have hm := outward_mem_blocks g bits ho
          rw [← h] at hm
          exact List.mem_append_left _ (List.mem_append_right _ hm)
        · have hs : target g a.1 = v := by
            have hh := congrArg (host g) h
            rw [host_reverse_outward] at hh
            exact hh.symm.trans hhost
          have hm := back_backward_mem_blocks g hg bits hb hs
          rw [← h] at hm
          exact List.mem_append_left _ (List.mem_append_right _ hm)

theorem directRow_perm_incident (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v < g.vertices) :
    (directRow g bits v).Perm (incidentRow g v) := by
  apply (List.perm_ext_iff_of_nodup (directRow_nodup g hg bits hv) (incidentRow_nodup g v)).mpr
  intro a
  rw [mem_directRow g hg bits hv,mem_incidentRow]

end PlanarHom.PlanarityLRDirect
