import PlanarHom.PolygonalArc

/-!
# Attach two straight tails to a simple polygonal middle arc

The first contacts along the two tails select simple prefixes/suffixes. The
result is a genuine polygonal graph edge: its only possible repeated points are
the two endpoints of a loop. No plane-arc tameness theorem is used.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chain
variable {U : Set E} {x y z : E}

/-- A simple polygonal prefix ending at any point of a simple chain. -/
theorem simple_prefix (p : Chain U x y) (hp : p.IsSimple) (z : E) (hz : z ∈ p.support) :
    ∃ q : Chain U x z, q.IsSimple ∧ q.support ⊆ p.support := by
  induction p with
  | nil x hx =>
    simp only [support_nil,mem_singleton_iff] at hz
    subst z
    exact ⟨.nil x hx,trivial,Subset.rfl⟩
  | @cons x a y h p ih =>
    rcases hp with ⟨hxa,hp,hinter⟩
    rw [support_cons] at hz ⊢
    rcases hz with hz | hz
    · by_cases hxz : x = z
      · subst z
        refine ⟨.nil x (h (left_mem_segment ℝ x a)),trivial,?_⟩
        simp only [support_nil,singleton_subset_iff]
        exact Or.inl (left_mem_segment ℝ x a)
      · have hseg : [x -[ℝ] z] ⊆ [x -[ℝ] a] :=
          (convex_segment x a).segment_subset (left_mem_segment ℝ x a) hz
        refine ⟨.segment (hseg.trans h),?_,?_⟩
        · exact ⟨hxz,trivial,fun w _ hw => by simpa only [support_nil,mem_singleton_iff] using hw⟩
        · rw [segment,support_cons,support_nil]
          exact union_subset (hseg.trans subset_union_left)
            (singleton_subset_iff.mpr (Or.inl hz))
    · obtain ⟨q,hq,hsub⟩ := ih hp hz
      refine ⟨.cons h q,⟨hxa,hq,?_⟩,?_⟩
      · intro w hw hwq
        exact hinter w hw (hsub hwq)
      · rw [support_cons]
        exact union_subset_union Subset.rfl hsub

@[simp] theorem support_append (p : Chain U x y) (q : Chain U y z) :
    (p.append q).support = p.support ∪ q.support := by
  induction p with
  | nil x hx =>
    simp only [append,support_nil]
    exact (union_eq_self_of_subset_left (singleton_subset_iff.mpr q.source_mem_support)).symm
  | cons h p ih => simp only [append,support_cons,ih,union_assoc]

/-- Simple chains concatenate whenever their supports meet just at the join. -/
theorem append_simple (p : Chain U x y) (q : Chain U y z)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = y) : (p.append q).IsSimple := by
  induction p with
  | nil x hx => exact hq
  | @cons x a y h p ih =>
    rcases hp with ⟨hxa,hp,hpinter⟩
    refine ⟨hxa,ih q hp hq (fun w hw hqw => hinter w (by rw [support_cons]; exact Or.inr hw) hqw),?_⟩
    intro w hw hwt
    rw [support_append] at hwt
    rcases hwt with hwp | hwq
    · exact hpinter w hw hwp
    · have hwy := hinter w (by rw [support_cons]; exact Or.inl hw) hwq
      exact hpinter w hw (hwy ▸ p.target_mem_support)

theorem segment_simple (h : [x -[ℝ] y] ⊆ U) (hxy : x ≠ y) : (Chain.segment h).IsSimple :=
  ⟨hxy,trivial,fun _ _ hw => by simpa only [support_nil,mem_singleton_iff] using hw⟩

/-- Change only the ambient containment set, keeping the same segment chain. -/
def mono : {x y : E} → (p : Chain U x y) → {W : Set E} → (U ⊆ W) → Chain W x y
  | _, _, .nil x hx, _, hUW => .nil x (hUW hx)
  | _, _, .cons h p, _, hUW => .cons (h.trans hUW) (p.mono hUW)

@[simp] theorem support_mono (p : Chain U x y) {W : Set E} (hUW : U ⊆ W) :
    (p.mono hUW).support = p.support := by
  induction p with
  | nil x hx => rfl
  | cons h p ih => simpa only [mono,support_cons] using congrArg (fun s => _ ∪ s) ih

theorem simple_mono (p : Chain U x y) (hp : p.IsSimple) {W : Set E} (hUW : U ⊆ W) :
    (p.mono hUW).IsSimple := by
  induction p with
  | nil x hx => trivial
  | cons h p ih =>
    exact ⟨hp.1,ih hp.2.1,by simpa only [support_mono] using hp.2.2⟩

end Chain

/-- Full equality classification for an arc whose endpoints may coincide. -/
def GraphArc {x y : E} (p : Path x y) : Prop :=
  ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

omit [NormedSpace ℝ E] in
/-- Gluing simple paths permits a closed loop, but no other repetitions. -/
theorem graphArc_trans {x y z : E} (p : Path x y) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : ∀ w, w ∈ Set.range p → w ∈ Set.range q → w = y ∨ (w = x ∧ x = z)) :
    GraphArc (p.trans q) := by
  intro s t h
  by_cases hs : (s : ℝ) ≤ 1/2
  · by_cases ht : (t : ℝ) ≤ 1/2
    · simp only [Path.trans_apply,dif_pos hs,dif_pos ht] at h
      have he := congrArg (fun a : I => (a : ℝ)) (hp h)
      left
      apply Subtype.ext
      change 2 * (s : ℝ) = 2 * (t : ℝ) at he
      linarith
    · simp only [Path.trans_apply,dif_pos hs,dif_neg ht] at h
      rcases hinter _ ⟨_,rfl⟩ ⟨_,h.symm⟩ with hj | ⟨hx,hxz⟩
      · have he := congrArg (fun a : I => (a : ℝ)) (hq (h.symm.trans (hj.trans q.source.symm)))
        change 2 * (t : ℝ) - 1 = 0 at he
        exfalso
        linarith
      · right; left
        have he₀ := congrArg (fun a : I => (a : ℝ)) (hp (hx.trans p.source.symm))
        have he₁ := congrArg (fun a : I => (a : ℝ))
          (hq (h.symm.trans (hx.trans (hxz.trans q.target.symm))))
        change 2 * (s : ℝ) = 0 at he₀
        change 2 * (t : ℝ) - 1 = 1 at he₁
        exact ⟨Subtype.ext (by simpa using (show (s : ℝ) = 0 by linarith)),
          Subtype.ext (by simpa using (show (t : ℝ) = 1 by linarith))⟩
  · by_cases ht : (t : ℝ) ≤ 1/2
    · simp only [Path.trans_apply,dif_neg hs,dif_pos ht] at h
      rcases hinter _ ⟨_,rfl⟩ ⟨_,h⟩ with hj | ⟨hx,hxz⟩
      · have he := congrArg (fun a : I => (a : ℝ)) (hq (h.trans (hj.trans q.source.symm)))
        change 2 * (s : ℝ) - 1 = 0 at he
        exfalso
        linarith
      · right; right
        have he₀ := congrArg (fun a : I => (a : ℝ)) (hp (hx.trans p.source.symm))
        have he₁ := congrArg (fun a : I => (a : ℝ))
          (hq (h.trans (hx.trans (hxz.trans q.target.symm))))
        change 2 * (t : ℝ) = 0 at he₀
        change 2 * (s : ℝ) - 1 = 1 at he₁
        exact ⟨Subtype.ext (by simpa using (show (s : ℝ) = 1 by linarith)),
          Subtype.ext (by simpa using (show (t : ℝ) = 0 by linarith))⟩
    · simp only [Path.trans_apply,dif_neg hs,dif_neg ht] at h
      have he := congrArg (fun a : I => (a : ℝ)) (hq h)
      left
      apply Subtype.ext
      change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at he
      linarith

/-- Attach two tails to a polygonal corridor path, trimming their contacts.
The tails may share their original endpoint, giving a loop. -/
theorem exists_attached_graphArc {U : Set E} {x y c d : E}
    (p : Chain U x y) (hp : p.IsSimple) (hc : c ∉ U) (hd : d ∉ U)
    (htails : ∀ w, w ∈ [c -[ℝ] x] → w ∈ [d -[ℝ] y] → w = c ∧ c = d) :
    ∃ q : Chain Set.univ c d, GraphArc q.strictPath ∧
      q.support ⊆ [c -[ℝ] x] ∪ U ∪ [d -[ℝ] y] := by
  obtain ⟨a,ha,hca,hSa,hainter⟩ := exists_first_contact p.isCompact_support
    (fun h => hc (p.support_subset h)) p.source_mem_support
  obtain ⟨pA,hpA,hpAsub⟩ := p.simple_suffix hp a ha
  obtain ⟨b,hb,hdb,hDb,hbinter⟩ := exists_first_contact pA.isCompact_support
    (fun h => hd (p.support_subset (hpAsub h))) pA.target_mem_support
  obtain ⟨pM,hpM,hpMsub⟩ := pA.simple_prefix hpA b hb
  have haU : a ∈ U := p.support_subset ha
  have had : a ≠ d := fun h => hd (h ▸ haU)
  have hMsub : pM.support ⊆ U := hpMsub.trans (hpAsub.trans p.support_subset)
  let m : Chain Set.univ a b := pM.mono (subset_univ _)
  have hm : m.IsSimple := pM.simple_mono hpM _
  have hmSupport : m.support = pM.support := pM.support_mono _
  let k : Chain Set.univ b d := Chain.segment (subset_univ _)
  have hk : k.IsSimple := Chain.segment_simple _ hdb.symm
  have hkSupport : k.support = [d -[ℝ] b] := by
    rw [← Chain.range_strictPath]
    change Set.range (Path.segment b d) = _
    rw [Path.range_segment,segment_symm]
  let tail := m.append k
  have htail : tail.IsSimple := m.append_simple k hm hk (by
    intro w hwm hwk
    rw [hmSupport] at hwm
    rw [hkSupport] at hwk
    exact hbinter w hwk (hpMsub hwm))
  have htailinj := tail.strictPath_injective htail had
  let q : Chain Set.univ c d := Chain.cons (subset_univ [c -[ℝ] a]) tail
  have hqPath : q.strictPath = (Path.segment c a).trans tail.strictPath := by
    change (Chain.cons (subset_univ [c -[ℝ] a]) tail).strictPath = _
    cases ht : tail with
    | nil a ha => exact (had rfl).elim
    | cons h t => rfl
  have hSrcinj : Function.Injective (Path.segment c a) := by
    intro s t h
    apply Subtype.ext
    exact AffineMap.lineMap_injective ℝ hca h
  refine ⟨q,?_,?_⟩
  · rw [hqPath]
    apply graphArc_trans _ _ hSrcinj htailinj
    intro w hwS hwT
    rw [Path.range_segment] at hwS
    rw [Chain.range_strictPath,Chain.support_append,hmSupport,hkSupport] at hwT
    rcases hwT with hwM | hwD
    · exact Or.inl (hainter w hwS (hpAsub (hpMsub hwM)))
    · exact Or.inr (htails w (hSa hwS) (hDb hwD))
  · change (Chain.cons (subset_univ [c -[ℝ] a]) tail).support ⊆ _
    rw [Chain.support_cons,Chain.support_append,hmSupport,hkSupport]
    rintro w (hw | hwM | hwD)
    · exact Or.inl (Or.inl (hSa hw))
    · exact Or.inl (Or.inr (hMsub hwM))
    · exact Or.inr (hDb hwD)

end PlanarHom.Polygonal
