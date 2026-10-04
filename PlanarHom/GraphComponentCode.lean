import PlanarHom.MixedPlanarCode
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Enum
import Mathlib.Logic.Relation

/-!
# Explicit connected-component occurrence codes

The program starts with one singleton for every vertex, including isolated
vertices, and processes the binary occurrences in order. An occurrence merges
precisely the parts containing one of its endpoints. Empty temporary parts are
removed at the end. Labels, loops, repeated edges and repeated unary factors
remain in the occurrence lists used by `extract`.
-/
namespace PlanarHom.GraphComponentCode
open Complexity

abbrev Edge := ℕ × (ℕ × ℕ)
abbrev Parts := List (List ℕ)

/-- Does this part contain either endpoint of the current occurrence? -/
def touches (e : Edge) (xs : List ℕ) : Bool :=
  decide (e.1 ∈ xs ∨ e.2.1 ∈ xs)

/-- Materialized union of the touched parts, followed by every untouched part.
The temporary empty union makes the function total even on invalid codes. -/
def merge (ps : Parts) (e : Edge) : Parts :=
  (ps.filter (touches e)).flatten :: ps.filter (fun xs => !(touches e xs))

/-- One original index per vertex, with a unary-charged explicit enumeration. -/
def initial (n : ℕ) : Parts := (List.range n).reverse.map (fun v => [v])

/-- Exact component vertex lists. Empty temporary unions are discarded. -/
def parts (g : MixedCode) : Parts :=
  (g.edges.foldl merge (initial g.vertices)).filter (fun xs => !xs.isEmpty)

/-- Retain a binary occurrence exactly when both of its endpoints are present. -/
def edgeInside (xs : List ℕ) (e : Edge) : Bool := decide (e.1 ∈ xs ∧ e.2.1 ∈ xs)

/-- Stable extraction uses the first local position of each original vertex.
Every surviving occurrence is mapped once, in its original order. -/
def extract (g : MixedCode) (xs : List ℕ) : MixedCode :=
  ⟨xs.length,
    (g.edges.filter (edgeInside xs)).map
      (fun e => (xs.idxOf e.1, xs.idxOf e.2.1, e.2.2)),
    (g.unaries.filter (fun u => decide (u.1 ∈ xs))).map
      (fun u => (xs.idxOf u.1, u.2))⟩

/-- The final list consists of ordinary mixed codes with local vertex indices. -/
def components (g : MixedCode) : List MixedCode := (parts g).map (extract g)

@[simp] theorem extract_vertices (g : MixedCode) (xs : List ℕ) :
    (extract g xs).vertices = xs.length := rfl

@[simp] theorem extract_edges_length (g : MixedCode) (xs : List ℕ) :
    (extract g xs).edges.length = (g.edges.filter (edgeInside xs)).length := by simp [extract]

@[simp] theorem extract_unaries_length (g : MixedCode) (xs : List ℕ) :
    (extract g xs).unaries.length = (g.unaries.filter (fun u => decide (u.1 ∈ xs))).length := by simp [extract]

theorem extract_valid {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (xs : List ℕ) :
    (extract g xs).Valid binaryTypes unaryTypes := by
  constructor
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨ha, hv⟩ := List.mem_filter.mp ha
    have hv' : a.1 ∈ xs ∧ a.2.1 ∈ xs := by simpa [edgeInside] using hv
    exact ⟨List.idxOf_lt_length_iff.mpr hv'.1, List.idxOf_lt_length_iff.mpr hv'.2,
      (hg.1 a ha).2.2⟩
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    obtain ⟨ha, hv⟩ := List.mem_filter.mp ha
    exact ⟨List.idxOf_lt_length_iff.mpr (by simpa using hv), (hg.2 a ha).2⟩

theorem parts_nonempty (g : MixedCode) (xs : List ℕ) (hx : xs ∈ parts g) : xs ≠ [] := by
  simpa only [parts, List.mem_filter, Bool.not_eq_true', List.isEmpty_eq_false_iff] using
    (List.mem_filter.mp hx).2

theorem components_nonempty (g : MixedCode) (c : MixedCode) (hc : c ∈ components g) :
    0 < c.vertices := by
  obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hc
  exact List.length_pos_iff.mpr (parts_nonempty g xs hx)

theorem components_valid {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (c : MixedCode) (hc : c ∈ components g) :
    c.Valid binaryTypes unaryTypes := by
  obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hc
  exact extract_valid g hg xs

end PlanarHom.GraphComponentCode
