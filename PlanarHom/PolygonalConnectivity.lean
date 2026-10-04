import PlanarHom.PlanarEmbedding
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Finite polygonal chains in open connected corridors

Reachability by finitely many line segments is proved open and relatively closed
inside an open subset of a real normed vector space. Thus every connected open
corridor admits finite polygonal chains. The chains contain explicit vertices
and segment-containment proofs; no simple-arc or loop-erasure claim is assumed.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Set
open scoped Convex unitInterval
namespace PlanarHom.Polygonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite chain of actual closed line segments contained in the corridor. -/
inductive Chain (U : Set E) : E → E → Type _
  | nil (x : E) (hx : x ∈ U) : Chain U x x
  | cons {x y z : E} (segment_subset : [x -[ℝ] y] ⊆ U) (tail : Chain U y z) : Chain U x z

namespace Chain
variable {U : Set E} {x y z : E}

/-- Number of line segments. -/
def length : {x y : E} → Chain U x y → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ p => p.length + 1

/-- The initial point belongs to the corridor. -/
theorem source_mem (p : Chain U x y) : x ∈ U := by
  cases p with
  | nil x hx => exact hx
  | cons h p => exact h (left_mem_segment ℝ _ _)

/-- The final point belongs to the corridor. -/
theorem target_mem (p : Chain U x y) : y ∈ U := by
  induction p with
  | nil x hx => exact hx
  | cons h p ih => exact ih

/-- Concatenate two finite chains at their common endpoint. -/
def append : {x y z : E} → Chain U x y → Chain U y z → Chain U x z
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons h p, q => .cons h (p.append q)

@[simp] theorem length_append (p : Chain U x y) (q : Chain U y z) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil x hx => simp [append, length]
  | cons h p ih => simp [append, length, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A single straight segment as a chain. -/
def segment (h : [x -[ℝ] y] ⊆ U) : Chain U x y :=
  .cons h (.nil y (h (right_mem_segment ℝ x y)))

@[simp] theorem length_segment (h : [x -[ℝ] y] ⊆ U) : (segment h).length = 1 := rfl

/-- Reverse all segments and their order. -/
def reverse : {x y : E} → Chain U x y → Chain U y x
  | _, _, .nil x hx => .nil x hx
  | _, _, .cons h p =>
      p.reverse.append (segment (by simpa only [segment_symm] using h))

@[simp] theorem length_reverse (p : Chain U x y) : p.reverse.length = p.length := by
  induction p with
  | nil x hx => rfl
  | cons h p ih => simp [reverse, length, ih]

/-- Interpret the finite list of segments as a genuine continuous path. -/
def toPath : {x y : E} → Chain U x y → Path x y
  | _, _, .nil x _ => .refl x
  | _, _, .cons _ p => (Path.segment _ _).trans p.toPath

/-- The genuine path never leaves the prescribed corridor. -/
theorem range_toPath_subset (p : Chain U x y) : Set.range p.toPath ⊆ U := by
  induction p with
  | nil x hx => simpa [toPath] using (singleton_subset_iff.mpr hx : ({x} : Set E) ⊆ U)
  | cons h p ih =>
      rw [toPath, Path.trans_range, Path.range_segment]
      exact union_subset h ih

/-- Explicitly record all vertices, including both endpoints. -/
def vertices : {x y : E} → Chain U x y → List E
  | _, _, .nil x _ => [x]
  | a, _, .cons _ p => a :: p.vertices

@[simp] theorem length_vertices (p : Chain U x y) : p.vertices.length = p.length + 1 := by
  induction p with
  | nil x hx => rfl
  | cons h p ih => simp [vertices, length, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Chain

/-- Actual finite segment-chain reachability, rather than arbitrary path reachability. -/
def Joined (U : Set E) (x y : E) : Prop := Nonempty (Chain U x y)

namespace Joined
variable {U : Set E} {x y z : E}

theorem refl (hx : x ∈ U) : Joined U x x := ⟨.nil x hx⟩
theorem trans (hxy : Joined U x y) (hyz : Joined U y z) : Joined U x z := by
  obtain ⟨p⟩ := hxy
  obtain ⟨q⟩ := hyz
  exact ⟨p.append q⟩
theorem symm (hxy : Joined U x y) : Joined U y x := by
  obtain ⟨p⟩ := hxy
  exact ⟨p.reverse⟩
theorem target_mem (hxy : Joined U x y) : y ∈ U := by
  obtain ⟨p⟩ := hxy
  exact p.target_mem

theorem of_segment (h : [x -[ℝ] y] ⊆ U) : Joined U x y := ⟨.segment h⟩

end Joined

/-- A reachable endpoint has a small reachable neighborhood. -/
theorem isOpen_joined {U : Set E} (hU : IsOpen U) (x : E) :
    IsOpen {y | Joined U x y} := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy.target_mem
  refine ⟨ε, hε, ?_⟩
  intro z hz
  exact hy.trans (.of_segment (Subset.trans
    ((convex_ball y ε).segment_subset (Metric.mem_ball_self hε) hz) hball))

/-- Unreachable points likewise have an unreachable neighborhood within the
open corridor: a short terminal segment would otherwise extend a chain. -/
theorem isOpen_not_joined {U : Set E} (hU : IsOpen U) (x : E) :
    IsOpen {y | y ∈ U ∧ ¬ Joined U x y} := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy.1
  refine ⟨ε, hε, ?_⟩
  intro z hz
  refine ⟨hball hz, fun h => hy.2 ?_⟩
  exact h.trans (.of_segment (Subset.trans
    ((convex_ball y ε).segment_subset hz (Metric.mem_ball_self hε)) hball))

/-- Every pair of points in an open preconnected corridor is joined by finitely
many straight segments inside that same corridor. -/
theorem joined_of_isOpen_isPreconnected {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) : Joined U x y := by
  have hd : Disjoint {z | Joined U x z} {z | z ∈ U ∧ ¬ Joined U x z} := by
    exact Set.disjoint_left.mpr (fun z hz hn => hn.2 hz)
  have hcover : U ⊆ {z | Joined U x z} ∪ {z | z ∈ U ∧ ¬ Joined U x z} := by
    intro z hz
    by_cases h : Joined U x z
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  have hs : (U ∩ {z | Joined U x z}).Nonempty := ⟨x, hx, Joined.refl hx⟩
  exact hconn.subset_left_of_subset_union (isOpen_joined hU x) (isOpen_not_joined hU x)
    hd hcover hs hy

/-- A shortest finite segment chain exists; later geometric shortcut arguments
can use this genuine minimum rather than assuming loop erasure. -/
theorem exists_minimal_chain {U : Set E} {x y : E} (h : Joined U x y) :
    ∃ p : Chain U x y, ∀ q : Chain U x y, p.length ≤ q.length := by
  have hex : ∃ n : ℕ, ∃ p : Chain U x y, p.length = n := by
    obtain ⟨p⟩ := h
    exact ⟨p.length, p, rfl⟩
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  refine ⟨p, fun q => ?_⟩
  rw [hp]
  exact Nat.find_min' hex ⟨q, rfl⟩

end PlanarHom.Polygonal
