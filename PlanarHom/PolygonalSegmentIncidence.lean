import PlanarHom.PolygonalAttachments
import PlanarHom.PolygonalBandGluing
import PlanarHom.PlanarNeighborhoods

/-!
# Actual segment incidence recovered from an embedded polygonal path

The half-interval parametrizations recover both component paths from their
concatenation. The ordinary graph-arc equality classification therefore forces
simple polygonal tails and rules out all non-endpoint segment intersections.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- Recover the first component path by its affine half-interval embedding. -/
theorem trans_left_half {x y z : X} (p : Path x y) (q : Path y z) (t : I) :
    (p.trans q) (MultiGraph.PlaneDrawing.halfParameter false t) = p t := by
  have ht : ((MultiGraph.PlaneDrawing.halfParameter false t : I) : ℝ) ≤ 1/2 := by
    change (t : ℝ)/2 ≤ 1/2
    linarith [t.2.2]
  rw [Path.trans_apply,dif_pos ht]
  apply congrArg p
  apply Subtype.ext
  dsimp [MultiGraph.PlaneDrawing.halfParameter]
  ring

omit [NormedSpace ℝ X] in
/-- Recover the second component, including the shared midpoint. -/
theorem trans_right_half {x y z : X} (p : Path x y) (q : Path y z) (t : I) :
    (p.trans q) (MultiGraph.PlaneDrawing.halfParameter true t) = q t := by
  by_cases ht0 : t = 0
  · subst t
    rw [MultiGraph.PlaneDrawing.halfParameter_true_zero,Path.trans_apply]
    norm_num [MultiGraph.PlaneDrawing.half]
  · have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm))
    have ht : ¬ (((MultiGraph.PlaneDrawing.halfParameter true t : I) : ℝ) ≤ 1/2) := by
      change ¬ ((1+(t : ℝ))/2 ≤ 1/2)
      linarith
    rw [Path.trans_apply,dif_neg ht]
    apply congrArg q
    apply Subtype.ext
    dsimp [MultiGraph.PlaneDrawing.halfParameter]
    ring

namespace GraphArc
variable {x y z : X} {p : Path x y} {q : Path y z}

omit [NormedSpace ℝ X] in
theorem left_injective (h : GraphArc (p.trans q)) : Function.Injective p := by
  intro s t heq
  have hh := h (MultiGraph.PlaneDrawing.halfParameter false s)
    (MultiGraph.PlaneDrawing.halfParameter false t) (by simpa only [trans_left_half] using heq)
  rcases hh with hh | ⟨_,ht⟩ | ⟨hs,_⟩
  · apply Subtype.ext
    have hc := congrArg (fun u : I => (u : ℝ)) hh
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith
  · have hc := congrArg (fun u : I => (u : ℝ)) ht
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith [t.2.2]
  · have hc := congrArg (fun u : I => (u : ℝ)) hs
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith [s.2.2]

omit [NormedSpace ℝ X] in
theorem right_injective (h : GraphArc (p.trans q)) : Function.Injective q := by
  intro s t heq
  have hh := h (MultiGraph.PlaneDrawing.halfParameter true s)
    (MultiGraph.PlaneDrawing.halfParameter true t) (by simpa only [trans_right_half] using heq)
  rcases hh with hh | ⟨hs,_⟩ | ⟨_,ht⟩
  · apply Subtype.ext
    have hc := congrArg (fun u : I => (u : ℝ)) hh
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith
  · have hc := congrArg (fun u : I => (u : ℝ)) hs
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith [s.2.1]
  · have hc := congrArg (fun u : I => (u : ℝ)) ht
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith [t.2.1]

omit [NormedSpace ℝ X] in
/-- The two component ranges meet only at their join, except for the allowed
coincidence of the original endpoints of a loop. -/
theorem component_intersection (h : GraphArc (p.trans q)) (w : X)
    (hp : w ∈ Set.range p) (hq : w ∈ Set.range q) : w = y ∨ (w = x ∧ x = z) := by
  obtain ⟨s,rfl⟩ := hp
  obtain ⟨t,heq⟩ := hq
  have hh := h (MultiGraph.PlaneDrawing.halfParameter false s)
    (MultiGraph.PlaneDrawing.halfParameter true t) (by simpa only [trans_left_half,trans_right_half] using heq.symm)
  rcases hh with hh | ⟨hs,ht⟩ | ⟨hs,_⟩
  · have hc := congrArg (fun u : I => (u : ℝ)) hh
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    have hs : s = 1 := Subtype.ext (by dsimp; linarith [s.2.2,t.2.1])
    left
    simp [hs]
  · have hc := congrArg (fun u : I => (u : ℝ)) hs
    have hd := congrArg (fun u : I => (u : ℝ)) ht
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc hd
    have hs0 : s = 0 := Subtype.ext (by dsimp; linarith)
    have ht1 : t = 1 := Subtype.ext (by dsimp; linarith)
    right
    exact ⟨by simp [hs0], by simpa [hs0,ht1] using heq.symm⟩
  · have hc := congrArg (fun u : I => (u : ℝ)) hs
    dsimp [MultiGraph.PlaneDrawing.halfParameter] at hc
    linarith [s.2.2]
end GraphArc

omit [NormedSpace ℝ X] in
theorem graphArc_of_injective {x y : X} {p : Path x y} (hp : Function.Injective p) : GraphArc p :=
  fun _ _ h => Or.inl (hp h)

omit [NormedSpace ℝ X] in
theorem endpoints_ne_of_path_injective {x y : X} {p : Path x y} (hp : Function.Injective p) : x ≠ y := by
  intro h
  have he := hp (p.source.trans (h.trans p.target.symm))
  have := congrArg (fun t : I => (t : ℝ)) he
  norm_num at this

namespace Chain
variable {U : Set X} {x y : X}

/-- An injectively parametrized finite polygonal chain has exactly the recursive
segment-separation property used by the local corner geometry. -/
theorem simple_of_strictPath_injective (p : Chain U x y) (hp : Function.Injective p.strictPath) :
    p.IsSimple := by
  induction p with
  | nil => trivial
  | @cons x a y h p ih =>
    cases p with
    | nil a ha =>
      exact ⟨endpoints_ne_of_path_injective hp,trivial,by
        intro w _ hw
        simpa only [support_nil,mem_singleton_iff] using hw⟩
    | @cons a b y k q =>
      have hgraph : GraphArc ((Path.segment x a).trans (Chain.cons k q).strictPath) :=
        graphArc_of_injective hp
      refine ⟨endpoints_ne_of_path_injective hgraph.left_injective,
        ih hgraph.right_injective,?_⟩
      intro w hw hwq
      have hh := hgraph.component_intersection w (by simpa only [Path.range_segment] using hw)
        (by simpa only [range_strictPath] using hwq)
      exact hh.resolve_right (fun h => endpoints_ne_of_path_injective hp h.2)

/-- The tail of any nontrivial polygonal graph edge is a simple chain, including
when the full edge is a loop. -/
theorem graphArc_cons_tail {a : X} (h : [x -[ℝ] a] ⊆ U) (p : Chain U a y)
    (hp : GraphArc (Chain.cons h p).strictPath) : p.IsSimple := by
  cases p with
  | nil => trivial
  | cons k q => exact (Chain.cons k q).simple_of_strictPath_injective hp.right_injective

/-- The source of a nontrivial simple chain is absent from its remaining tail. -/
theorem simple_source_notMem_tail {a : X} (h : [x -[ℝ] a] ⊆ U) (p : Chain U a y)
    (hp : (Chain.cons h p).IsSimple) : x ∉ p.support := by
  intro hx
  exact hp.1 (hp.2.2 x (left_mem_segment ℝ x a) hx)

/-- No segment of a simple chain ends at its source. -/
theorem simple_no_incoming_source (p : Chain U x y) (hp : p.IsSimple) (a : X) :
    (a,x) ∉ p.segments := by
  cases p with
  | nil => simp [segments]
  | @cons x b y h p =>
    intro ha
    rcases List.mem_cons.mp ha with heq | ha
    · exact hp.1 (congrArg Prod.snd heq)
    · exact simple_source_notMem_tail h p hp
        (p.segment_subset_support ha (right_mem_segment ℝ a x))

/-- Exactly the first segment can start at the source of a simple chain. -/
theorem simple_outgoing_source_unique {a : X} (h : [x -[ℝ] a] ⊆ U) (p : Chain U a y)
    (hp : (Chain.cons h p).IsSimple) {b : X} (hb : (x,b) ∈ (Chain.cons h p).segments) : b = a := by
  rcases List.mem_cons.mp hb with heq | hb
  · exact (congrArg Prod.snd heq)
  · exact (simple_source_notMem_tail h p hp
      (p.segment_subset_support hb (left_mem_segment ℝ x b))).elim

/-- Every non-endpoint chain vertex has one incoming and one outgoing segment. -/
theorem simple_internal_incidence (p : Chain U x y) (hp : p.IsSimple) (v : X)
    (hvx : v ≠ x) (hvy : v ≠ y)
    (hv : ∃ a b, (a,b) ∈ p.segments ∧ (a = v ∨ b = v)) :
    ∃ P Q, P ≠ v ∧ v ≠ Q ∧
      (∀ z, z ∈ [P -[ℝ] v] → z ∈ [v -[ℝ] Q] → z = v) ∧
      (∀ a b, (a,b) ∈ p.segments → a = v → b = Q) ∧
      (∀ a b, (a,b) ∈ p.segments → b = v → a = P) := by
  induction p with
  | nil => simp [segments] at hv
  | @cons x a y h p ih =>
    by_cases hva : v = a
    · subst v
      cases p with
      | nil => exact (hvy rfl).elim
      | @cons a b y k q =>
        refine ⟨x,b,hp.1,hp.2.1.1,?_,?_,?_⟩
        · intro z hz hz'
          exact hp.2.2 z hz (by rw [support_cons]; exact Or.inl hz')
        · intro c d hcd hc
          subst c
          rcases List.mem_cons.mp hcd with heq | hcd
          · exact (hp.1 (congrArg Prod.fst heq).symm).elim
          · exact simple_outgoing_source_unique k q hp.2.1 hcd
        · intro c d hcd hd
          subst d
          rcases List.mem_cons.mp hcd with heq | hcd
          · exact congrArg Prod.fst heq
          · exact ((Chain.cons k q).simple_no_incoming_source hp.2.1 c hcd).elim
    · have hvtail : ∃ c d, (c,d) ∈ p.segments ∧ (c = v ∨ d = v) := by
        obtain ⟨c,d,hcd,hv⟩ := hv
        rcases List.mem_cons.mp hcd with heq | hcd
        · cases heq
          exact (hv.elim (fun h => hvx h.symm) (fun h => hva h.symm)).elim
        · exact ⟨c,d,hcd,hv⟩
      obtain ⟨P,Q,hPv,hvQ,hcorner,hout,hin⟩ := ih hp.2.1 hva hvy hvtail
      refine ⟨P,Q,hPv,hvQ,hcorner,?_,?_⟩
      · intro c d hcd hc
        rcases List.mem_cons.mp hcd with heq | hcd
        · cases heq
          exact (hvx hc.symm).elim
        · exact hout c d hcd hc
      · intro c d hcd hd
        rcases List.mem_cons.mp hcd with heq | hcd
        · cases heq
          exact (hva hd.symm).elim
        · exact hin c d hcd hd

end Chain

/-- Allowing both endpoints in a corner-intersection statement adds no genuine
intersection: if the extra endpoint occurred, an interior midpoint would too. -/
theorem corner_intersection_of_endpoints (P Q R : X) (hPQ : P ≠ Q)
    (h : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [Q -[ℝ] R] → z = Q ∨ z = P) :
    ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [Q -[ℝ] R] → z = Q := by
  intro z hz hz'
  rcases h z hz hz' with hQ | hP
  · exact hQ
  · have hPR : P ∈ [Q -[ℝ] R] := hP ▸ hz'
    let M := AffineMap.lineMap P Q (1/2 : ℝ)
    have hM : M ∈ [P -[ℝ] Q] := by
      rw [segment_eq_image_lineMap]
      exact ⟨1/2,by constructor <;> norm_num,rfl⟩
    have hM' : M ∈ [Q -[ℝ] R] :=
      (convex_segment Q R).segment_subset hPR (left_mem_segment ℝ Q R) hM
    rcases h M hM hM' with hMQ | hMP
    · have he := AffineMap.lineMap_injective ℝ hPQ (hMQ.trans (AffineMap.lineMap_apply_one P Q).symm)
      norm_num at he
    · have he := AffineMap.lineMap_injective ℝ hPQ (hMP.trans (AffineMap.lineMap_apply_zero P Q).symm)
      norm_num at he

namespace Chain
variable {U : Set X} {x y : X}

/-- Exact valence-two corners also hold in a polygonal graph edge that may be a loop. -/
theorem graphArc_internal_incidence (p : Chain U x y) (hp : GraphArc p.strictPath) (v : X)
    (hvx : v ≠ x) (hvy : v ≠ y)
    (hv : ∃ a b, (a,b) ∈ p.segments ∧ (a = v ∨ b = v)) :
    ∃ P Q, P ≠ v ∧ v ≠ Q ∧
      (∀ z, z ∈ [P -[ℝ] v] → z ∈ [v -[ℝ] Q] → z = v) ∧
      (∀ a b, (a,b) ∈ p.segments → a = v → b = Q) ∧
      (∀ a b, (a,b) ∈ p.segments → b = v → a = P) := by
  cases p with
  | nil => simp [segments] at hv
  | @cons x a y h p =>
    cases p with
    | nil =>
      obtain ⟨c,d,hcd,hv⟩ := hv
      have heq : (c,d) = (x,y) := by simpa [segments] using hcd
      cases heq
      exact (hv.elim (fun h => hvx h.symm) (fun h => hvy h.symm)).elim
    | @cons a b y k q =>
      have htail : (Chain.cons k q).IsSimple :=
        (Chain.cons k q).simple_of_strictPath_injective hp.right_injective
      have hxa : x ≠ a := endpoints_ne_of_path_injective hp.left_injective
      by_cases hva : v = a
      · subst v
        refine ⟨x,b,hxa,htail.1,?_,?_,?_⟩
        · apply corner_intersection_of_endpoints x a b hxa
          intro z hz hz'
          have hh := hp.component_intersection z
            (by simpa only [Path.range_segment] using hz)
            (by rw [Chain.range_strictPath,Chain.support_cons]; exact Or.inl hz')
          exact hh.imp_right And.left
        · intro c d hcd hc
          subst c
          rcases List.mem_cons.mp hcd with heq | hcd
          · exact (hxa (congrArg Prod.fst heq).symm).elim
          · exact simple_outgoing_source_unique k q htail hcd
        · intro c d hcd hd
          subst d
          rcases List.mem_cons.mp hcd with heq | hcd
          · exact congrArg Prod.fst heq
          · exact ((Chain.cons k q).simple_no_incoming_source htail c hcd).elim
      · have hvtail : ∃ c d, (c,d) ∈ (Chain.cons k q).segments ∧ (c = v ∨ d = v) := by
          obtain ⟨c,d,hcd,hv⟩ := hv
          rcases List.mem_cons.mp hcd with heq | hcd
          · cases heq
            exact (hv.elim (fun h => hvx h.symm) (fun h => hva h.symm)).elim
          · exact ⟨c,d,hcd,hv⟩
        obtain ⟨P,Q,hPv,hvQ,hcorner,hout,hin⟩ :=
          (Chain.cons k q).simple_internal_incidence htail v hva hvy hvtail
        refine ⟨P,Q,hPv,hvQ,hcorner,?_,?_⟩
        · intro c d hcd hc
          rcases List.mem_cons.mp hcd with heq | hcd
          · cases heq
            exact (hvx hc.symm).elim
          · exact hout c d hcd hc
        · intro c d hcd hd
          rcases List.mem_cons.mp hcd with heq | hcd
          · cases heq
            exact (hva hd.symm).elim
          · exact hin c d hcd hd

/-- The affine half-interval maps are strictly increasing even at endpoints. -/
theorem halfParameter_strictMono (b : Bool) : StrictMono (MultiGraph.PlaneDrawing.halfParameter b) := by
  intro s t hst
  cases b <;> change (_ : ℝ) < _ <;> dsimp [MultiGraph.PlaneDrawing.halfParameter] <;>
    exact (by have hh : (s : ℝ) < t := hst; linarith)

/-- Every actual segment occurrence has an increasing affine global subpath.
Strict local interior parameters map to strict global interior parameters. -/
theorem segment_subpath (p : Chain U x y) {a b : X} (hab : (a,b) ∈ p.segments) :
    ∃ f : C(I,I), StrictMono f ∧
      (∀ t : I, MultiGraph.Inside t → MultiGraph.Inside (f t)) ∧
      ∀ t : I, p.strictPath (f t) = AffineMap.lineMap a b (t : ℝ) := by
  induction p with
  | nil => simp [segments] at hab
  | @cons x c y h p ih =>
    cases p with
    | nil c hc =>
      have heq : (a,b) = (x,c) := by simpa [segments] using hab
      cases heq
      exact ⟨ContinuousMap.id I,strictMono_id,fun _ ht => ht,fun _ => rfl⟩
    | @cons c d y k q =>
      rcases List.mem_cons.mp hab with heq | hab
      · cases heq
        refine ⟨MultiGraph.PlaneDrawing.halfParameter false,halfParameter_strictMono false,
          fun _ ht => MultiGraph.PlaneDrawing.halfParameter_inside false ht,?_⟩
        intro t
        exact trans_left_half (Path.segment _ _) (Chain.cons k q).strictPath t
      · obtain ⟨f,hf,hinside,hpath⟩ := ih hab
        refine ⟨(MultiGraph.PlaneDrawing.halfParameter true).comp f,
          (halfParameter_strictMono true).comp hf,
          fun t ht => MultiGraph.PlaneDrawing.halfParameter_inside true (hinside t ht),?_⟩
        intro t
        exact (trans_right_half (Path.segment x c) (Chain.cons k q).strictPath (f t)).trans (hpath t)

/-- No geometric segment of a polygonal graph arc is degenerate. -/
theorem graphArc_segment_ne (p : Chain U x y) (hp : GraphArc p.strictPath)
    {a b : X} (hab : (a,b) ∈ p.segments) : a ≠ b := by
  intro heq
  obtain ⟨f,hf,hinside,hpath⟩ := p.segment_subpath hab
  have h₁ := hinside MultiGraph.PlaneDrawing.firstThird MultiGraph.PlaneDrawing.firstThird_inside
  have h₂ := hinside MultiGraph.PlaneDrawing.secondThird MultiGraph.PlaneDrawing.secondThird_inside
  have hsame : p.strictPath (f MultiGraph.PlaneDrawing.firstThird) =
      p.strictPath (f MultiGraph.PlaneDrawing.secondThird) := by rw [hpath,hpath,heq]; simp
  rcases hp _ _ hsame with h | ⟨h,_⟩ | ⟨h,_⟩
  · exact MultiGraph.PlaneDrawing.firstThird_lt_secondThird.ne (hf.injective h)
  · simp [MultiGraph.Inside,h] at h₁
  · simp [MultiGraph.Inside,h] at h₁

end Chain
end PlanarHom.Polygonal
