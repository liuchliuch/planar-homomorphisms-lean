import PlanarHom.PolygonalStrips

/-!
# Joint-continuous global bands from finite polygonal chains

An arbitrary map of the finite chain vertices gives a second genuine polygonal
path with exactly the same parametrization pattern. Linear interpolation between
the two paths is jointly continuous. Every point has a simultaneous original and
mapped representation on one actual segment occurrence, so the global band is
exactly one of the explicit local bilinear strips.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Chain
variable {U : Set E} {x y : E}

/-- Map only the finitely many vertices. No continuity of the vertex map is needed. -/
def mapVertices (f : E → E) : {x y : E} → Chain U x y → Chain Set.univ (f x) (f y)
  | _, _, .nil x _ => .nil (f x) (Set.mem_univ _)
  | _, _, .cons _ p => .cons (subset_univ _) (p.mapVertices f)

@[simp] theorem length_mapVertices (p : Chain U x y) (f : E → E) :
    (p.mapVertices f).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [mapVertices,length,ih]

/-- Ordered segment occurrences, with multiplicity and orientation retained. -/
def segments : {x y : E} → Chain U x y → List (E × E)
  | _, _, .nil _ _ => []
  | x, _, @Chain.cons _ _ _ _ _ a _ _ p => (x,a) :: p.segments

@[simp] theorem length_segments (p : Chain U x y) : p.segments.length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [segments,length,ih]

@[simp] theorem segments_mapVertices (p : Chain U x y) (f : E → E) :
    (p.mapVertices f).segments = p.segments.map (fun q => (f q.1,f q.2)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [segments,mapVertices,ih]

theorem segment_subset_support (p : Chain U x y) {a b : E} (hab : (a,b) ∈ p.segments) :
    [a -[ℝ] b] ⊆ p.support := by
  induction p with
  | nil => simp [segments] at hab
  | cons h p ih =>
    rcases List.mem_cons.mp hab with hpair | htail
    · cases hpair
      rw [support_cons]
      exact subset_union_left
    · rw [support_cons]
      exact (ih htail).trans subset_union_right

/-- Simultaneous local coordinates for the old and vertex-mapped paths.
The same segment occurrence and the same local parameter represent both values. -/
theorem strictPath_joint_segment (p : Chain U x y) (hn : p.length ≠ 0) (f : E → E) (t : I) :
    ∃ a b, (a,b) ∈ p.segments ∧ ∃ u : I,
      p.strictPath t = AffineMap.lineMap a b (u : ℝ) ∧
      (p.mapVertices f).strictPath t = AffineMap.lineMap (f a) (f b) (u : ℝ) := by
  induction p generalizing t with
  | nil => exact (hn rfl).elim
  | @cons x a y h p ih =>
    cases p with
    | nil a ha => exact ⟨x,a,by simp [segments],t,rfl,rfl⟩
    | @cons a b y k q =>
      by_cases ht : (t : ℝ) ≤ 1/2
      · let u : I := ⟨2*(t : ℝ),by constructor <;> linarith [t.2.1]⟩
        refine ⟨x,a,by simp [segments],u,?_,?_⟩
        · simp only [strictPath,Path.trans_apply,dif_pos ht]
          rfl
        · simp only [mapVertices,strictPath,Path.trans_apply,dif_pos ht]
          rfl
      · let u : I := ⟨2*(t : ℝ)-1,by constructor <;> linarith [t.2.2]⟩
        obtain ⟨c,d,hcd,v,hv,hfv⟩ := ih (by simp [length]) u
        refine ⟨c,d,List.mem_cons_of_mem _ hcd,v,?_,?_⟩
        · simpa only [strictPath,Path.trans_apply,dif_neg ht] using hv
        · simpa only [mapVertices,strictPath,Path.trans_apply,dif_neg ht] using hfv

/-- Interpolate two actual paths, jointly in longitudinal and transverse coordinates. -/
def vertexBand (p : Chain U x y) (f : E → E) : C(I × I,E) where
  toFun q := p.strictPath q.1 + (q.2 : ℝ) • ((p.mapVertices f).strictPath q.1 - p.strictPath q.1)
  continuous_toFun := by fun_prop

@[simp] theorem vertexBand_zero_transverse (p : Chain U x y) (f : E → E) (t : I) :
    p.vertexBand f (t,0) = p.strictPath t := by simp [vertexBand]

@[simp] theorem vertexBand_source (p : Chain U x y) (f : E → E) (hf : f x = x) (s : I) :
    p.vertexBand f (0,s) = x := by simp [vertexBand,hf]

@[simp] theorem vertexBand_target (p : Chain U x y) (f : E → E) (hf : f y = y) (s : I) :
    p.vertexBand f (1,s) = y := by simp [vertexBand,hf]

end Chain

namespace Chain
open MultiGraph
variable {U : Set Plane} {x y : Plane}

/-- Exact agreement with one of the proved bilinear local strip formulas. -/
theorem vertexBand_local_strip (p : Chain U x y) (hn : p.length ≠ 0) (f : Plane → Plane)
    (t s : I) : ∃ a b, (a,b) ∈ p.segments ∧ ∃ u : I,
      p.strictPath t = AffineMap.lineMap a b (u : ℝ) ∧
      p.vertexBand f (t,s) = stripMap a b (f a-a) (f b-b) (u,s) := by
  obtain ⟨a,b,hab,u,hu,hfu⟩ := p.strictPath_joint_segment hn f t
  refine ⟨a,b,hab,u,hu,?_⟩
  change p.strictPath t + (s : ℝ) • ((p.mapVertices f).strictPath t - p.strictPath t) = _
  rw [hu,hfu]
  apply Prod.ext <;> simp [stripMap,strip,AffineMap.lineMap_apply_module] <;> ring

/-- A common width applied to fixed vertex offsets gives the precise local
cross-sections used by the small-width geometric separation theorems. -/
theorem vertexBand_offset_local_strip (p : Chain U x y) (hn : p.length ≠ 0)
    (N : Plane → Plane) (ε : ℝ) (t s : I) :
    ∃ a b, (a,b) ∈ p.segments ∧ ∃ u : I,
      p.strictPath t = AffineMap.lineMap a b (u : ℝ) ∧
      p.vertexBand (fun v => v + ε • N v) (t,s) = stripMap a b (ε • N a) (ε • N b) (u,s) := by
  simpa only [add_sub_cancel_left] using
    p.vertexBand_local_strip hn (fun v => v + ε • N v) t s

end Chain
end PlanarHom.Polygonal
