import PlanarHom.PolygonalConnectivity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

/-!
# Loop erasure for finite polygonal chains

The construction repeatedly joins a new initial segment to the first point where
it meets the compact support of an already simple polygonal tail. Every retained
subsegment stays inside the original corridor.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Set
open scoped Convex unitInterval
namespace PlanarHom.Polygonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Chain
variable {U : Set E} {x y z : E}

/-- The finite union of the chain's actual line segments. -/
def support (p : Chain U x y) : Set E := Set.range p.toPath

@[simp] theorem support_nil (x : E) (hx : x ∈ U) : (Chain.nil x hx).support = {x} := by
  simp [support, toPath]

@[simp] theorem support_cons (h : [x -[ℝ] y] ⊆ U) (p : Chain U y z) :
    (Chain.cons h p).support = [x -[ℝ] y] ∪ p.support := by
  simp only [support, toPath, Path.trans_range, Path.range_segment]

theorem support_subset (p : Chain U x y) : p.support ⊆ U := p.range_toPath_subset

theorem source_mem_support (p : Chain U x y) : x ∈ p.support := p.toPath.source_mem_range

theorem target_mem_support (p : Chain U x y) : y ∈ p.support := p.toPath.target_mem_range

theorem isCompact_support (p : Chain U x y) : IsCompact p.support :=
  isCompact_range p.toPath.continuous

/-- Consecutive segments are nondegenerate and each initial segment meets the
remaining chain only at their common endpoint. -/
def IsSimple : {x y : E} → Chain U x y → Prop
  | _, _, .nil _ _ => True
  | x, _, @Chain.cons _ _ _ _ _ y _ _ p =>
      x ≠ y ∧ p.IsSimple ∧ ∀ w, w ∈ [x -[ℝ] y] → w ∈ p.support → w = y

/-- Any point of a simple polygonal chain begins a simple polygonal suffix,
whose support stays inside the original chain. -/
theorem simple_suffix (p : Chain U x y) (hp : p.IsSimple) (z : E) (hz : z ∈ p.support) :
    ∃ q : Chain U z y, q.IsSimple ∧ q.support ⊆ p.support := by
  induction p with
  | nil x hx =>
      simp only [support_nil, mem_singleton_iff] at hz
      subst z
      exact ⟨.nil x hx, trivial, Subset.rfl⟩
  | @cons x a y h p ih =>
      rcases hp with ⟨hxa, hp, hinter⟩
      rw [support_cons] at hz ⊢
      rcases hz with hz | hz
      · by_cases hza : z = a
        · subst z
          exact ⟨p, hp, subset_union_right⟩
        · have hsub : [z -[ℝ] a] ⊆ [x -[ℝ] a] :=
            (convex_segment x a).segment_subset hz (right_mem_segment ℝ x a)
          refine ⟨.cons (hsub.trans h) p, ⟨hza, hp, ?_⟩, ?_⟩
          · intro w hw hwq
            exact hinter w (hsub hw) hwq
          · rw [support_cons]
            exact union_subset_union hsub Subset.rfl
      · obtain ⟨q, hq, hsub⟩ := ih hp hz
        exact ⟨q, hq, hsub.trans subset_union_right⟩

end Chain

/-- The first intersection of a segment with a nonempty compact target leaves
an initial subsegment meeting that target at just its final endpoint. -/
theorem exists_first_contact {K : Set E} (hK : IsCompact K) {x y : E}
    (hx : x ∉ K) (hy : y ∈ K) :
    ∃ z ∈ K, x ≠ z ∧ [x -[ℝ] z] ⊆ [x -[ℝ] y] ∧
      ∀ w, w ∈ [x -[ℝ] z] → w ∈ K → w = z := by
  let T : Set ℝ := Set.Icc 0 1 ∩ (AffineMap.lineMap x y) ⁻¹' K
  have hT : IsCompact T := isCompact_Icc.inter_right
    (hK.isClosed.preimage (by fun_prop))
  have h1 : (1 : ℝ) ∈ T := by simp [T, hy]
  obtain ⟨t, ht, hmin⟩ := hT.exists_isLeast ⟨1, h1⟩
  let z := AffineMap.lineMap x y t
  have hz : z ∈ K := ht.2
  have hzseg : z ∈ [x -[ℝ] y] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht.1, rfl⟩
  refine ⟨z, hz, fun h => hx (h ▸ hz),
    (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hzseg, ?_⟩
  intro w hw hwK
  rw [segment_eq_image_lineMap] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  have heq : AffineMap.lineMap x z s = AffineMap.lineMap x y (s * t) := by
    simp only [z, AffineMap.lineMap_apply_module, smul_add, smul_smul]
    module
  have hst : s * t ∈ T := by
    refine ⟨⟨mul_nonneg hs.1 ht.1.1, ?_⟩, ?_⟩
    · nlinarith [hs.2, ht.1.1, ht.1.2]
    · change AffineMap.lineMap x y (s * t) ∈ K
      rw [← heq]
      exact hwK
  have hle : t ≤ s * t := hmin hst
  have hEq : s * t = t := by nlinarith [hs.2, ht.1.1]
  rw [heq, hEq]

/-- Genuine finite polygonal loop erasure, retaining a subset of the original
support. No topological tameness or Jordan theorem is assumed. -/
theorem Chain.exists_simple {U : Set E} {x y : E} (p : Chain U x y) :
    ∃ q : Chain U x y, q.IsSimple ∧ q.support ⊆ p.support := by
  induction p with
  | nil x hx => exact ⟨.nil x hx, trivial, Subset.rfl⟩
  | @cons x a y h p ih =>
      obtain ⟨q, hq, hsub⟩ := ih
      by_cases hx : x ∈ q.support
      · obtain ⟨r, hr, hrsub⟩ := q.simple_suffix hq x hx
        exact ⟨r, hr, hrsub.trans (hsub.trans (by rw [Chain.support_cons]; exact subset_union_right))⟩
      · obtain ⟨z, hz, hxz, hzseg, hinter⟩ :=
          exists_first_contact q.isCompact_support hx q.source_mem_support
        obtain ⟨r, hr, hrsub⟩ := q.simple_suffix hq z hz
        refine ⟨.cons (hzseg.trans h) r, ⟨hxz, hr, ?_⟩, ?_⟩
        · intro w hw hwr
          exact hinter w hw (hrsub hwr)
        · rw [Chain.support_cons, Chain.support_cons]
          exact union_subset_union hzseg (hrsub.trans hsub)

/-- An open connected corridor contains a simple finite polygonal chain between
any two selected points. -/
theorem exists_simple_chain_of_isOpen_isPreconnected {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ p : Chain U x y, p.IsSimple := by
  obtain ⟨p⟩ := joined_of_isOpen_isPreconnected hU hconn hx hy
  obtain ⟨q, hq, _⟩ := p.exists_simple
  exact ⟨q, hq⟩


/-- Concatenation is injective when both component paths are injective and their
ranges meet only at the common endpoint. -/
theorem path_trans_injective {x y z : E} (p : Path x y) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : ∀ w, w ∈ Set.range p → w ∈ Set.range q → w = y) :
    Function.Injective (p.trans q) := by
  intro s t h
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [Path.trans_apply, dif_pos hs, dif_pos ht] at h
      have he := congrArg (fun a : unitInterval => (a : ℝ)) (hp h)
      apply Subtype.ext
      change 2 * (s : ℝ) = 2 * (t : ℝ) at he
      linarith
    · simp only [Path.trans_apply, dif_pos hs, dif_neg ht] at h
      have hb := hinter _ ⟨_, rfl⟩ ⟨_, h.symm⟩
      have h0 := congrArg (fun a : unitInterval => (a : ℝ))
        (hq (h.symm.trans (hb.trans q.source.symm)))
      change 2 * (t : ℝ) - 1 = 0 at h0
      exfalso
      linarith
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [Path.trans_apply, dif_neg hs, dif_pos ht] at h
      have hb := hinter _ ⟨_, rfl⟩ ⟨_, h⟩
      have h0 := congrArg (fun a : unitInterval => (a : ℝ))
        (hq (h.trans (hb.trans q.source.symm)))
      change 2 * (s : ℝ) - 1 = 0 at h0
      exfalso
      linarith
    · simp only [Path.trans_apply, dif_neg hs, dif_neg ht] at h
      have he := congrArg (fun a : unitInterval => (a : ℝ)) (hq h)
      apply Subtype.ext
      change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at he
      linarith

namespace Chain
variable {U : Set E} {x y z : E}

/-- Concatenate only the nonempty list of segments, with no artificial constant
path added at the endpoint. -/
def strictPath : {x y : E} → Chain U x y → Path x y
  | _, _, .nil x _ => .refl x
  | _, _, .cons _ (.nil _ _) => Path.segment _ _
  | _, _, .cons _ (.cons h p) => (Path.segment _ _).trans (strictPath (.cons h p))

/-- Removing the artificial terminal pause changes no drawn point. -/
theorem range_strictPath (p : Chain U x y) : Set.range p.strictPath = p.support := by
  induction p with
  | nil x hx => simp [strictPath]
  | cons h p ih =>
      cases p with
      | nil a ha =>
          simp only [strictPath, Path.range_segment, support_cons, support_nil]
          exact (union_eq_self_of_subset_right (singleton_subset_iff.mpr
            (right_mem_segment ℝ _ _))).symm
      | cons k q =>
          simpa only [strictPath, Path.trans_range, Path.range_segment, support_cons] using
            congrArg (fun S : Set E => _ ∪ S) ih

/-- A nonempty simple chain has distinct endpoints. -/
theorem ne_endpoints_of_simple_cons (h : [x -[ℝ] y] ⊆ U) (p : Chain U y z)
    (hp : (Chain.cons h p).IsSimple) : x ≠ z := by
  intro hxz
  apply hp.1
  apply hp.2.2 x (left_mem_segment ℝ x y)
  rw [hxz]
  exact p.target_mem_support

/-- The strict parametrization of a nontrivial simple polygonal chain is an
injective actual continuous path. -/
theorem strictPath_injective (p : Chain U x y) (hp : p.IsSimple) (hxy : x ≠ y) :
    Function.Injective p.strictPath := by
  induction p with
  | nil x hx => exact (hxy rfl).elim
  | @cons x a y h p ih =>
      rcases hp with ⟨hxa, hp, hinter⟩
      have hseg : Function.Injective (Path.segment x a) := by
        intro s t heq
        apply Subtype.ext
        exact AffineMap.lineMap_injective ℝ hxa heq
      cases p with
      | nil a ha => exact hseg
      | cons k q =>
          apply path_trans_injective (Path.segment x a) (Chain.cons k q).strictPath hseg
          · exact ih hp (ne_endpoints_of_simple_cons k q hp)
          · intro w hw hwq
            rw [Path.range_segment] at hw
            rw [range_strictPath] at hwq
            exact hinter w hw hwq

end Chain

/-- An actual injective polygonal arc through an arbitrary connected open
corridor, with explicit finite segment data and exact endpoints. -/
theorem exists_injective_polygonal_arc {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ p : Chain U x y, p.IsSimple ∧ Function.Injective p.strictPath ∧
      Set.range p.strictPath ⊆ U := by
  obtain ⟨p, hp⟩ := exists_simple_chain_of_isOpen_isPreconnected hU hconn hx hy
  exact ⟨p, hp, p.strictPath_injective hp hxy, p.range_strictPath ▸ p.support_subset⟩

end PlanarHom.Polygonal
