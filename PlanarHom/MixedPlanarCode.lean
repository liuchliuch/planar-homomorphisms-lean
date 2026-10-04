import PlanarHom.PlanarGraphCode
import PlanarHom.PlanarTransport

/-!
# Ordinary planarity for mixed binary/unary occurrence codes

For planarity, binary labels are forgotten and unary occurrences do not add
vertices or edges. Label/domain validity is retained as a separate part of the
mixed promise. No embedding certificate or recognition algorithm is assumed.
-/

namespace PlanarHom.Complexity.MixedCode

/-- Forget only binary labels; preserve vertex count, edge order, loops and
parallel occurrences. Unary factors have no additional graph incidence. -/
def underlying (g : MixedCode) : GraphCode :=
  ⟨g.vertices, g.edges.map (fun e => (e.1,e.2.1))⟩

@[simp] theorem underlying_vertices (g : MixedCode) : g.underlying.vertices = g.vertices := rfl
@[simp] theorem underlying_edges_length (g : MixedCode) :
    g.underlying.edges.length = g.edges.length := by simp [underlying]

theorem underlying_valid {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (h : g.Valid binaryTypes unaryTypes) : g.underlying.Valid := by
  rintro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact ⟨(h.1 a ha).1,(h.1 a ha).2.1⟩

/-- Direct incidence interpretation indexed by the original labelled occurrence
positions. This does not drop labels from the computational instance itself. -/
def toMultiGraph {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (h : g.Valid binaryTypes unaryTypes) :
    MultiGraph (Fin g.vertices) (Fin g.edges.length) where
  src e := ⟨(g.edges.get e).1,(h.1 _ (List.get_mem _ _)).1⟩
  dst e := ⟨(g.edges.get e).2.1,(h.1 _ (List.get_mem _ _)).2.1⟩

/-- The direct incidence graph is exactly the label-forgotten GraphCode graph,
with only the definitional length cast on occurrence indices. -/
def underlyingIncidenceEquiv {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (h : g.Valid binaryTypes unaryTypes) :
    MultiGraph.IncidenceEquiv (g.toMultiGraph h)
      (g.underlying.toMultiGraph (g.underlying_valid h)) where
  vertex := Equiv.refl _
  edge := finCongr g.underlying_edges_length.symm
  src_eq e := by apply Fin.ext; simp [GraphCode.toMultiGraph, toMultiGraph, underlying]
  dst_eq e := by apply Fin.ext; simp [GraphCode.toMultiGraph, toMultiGraph, underlying]

/-- Full ordinary mixed-input promise: fixed label bounds plus underlying
abstract planarity. It does not depend on serialized drawings. -/
def PlanarValid (binaryTypes unaryTypes : ℕ) (g : MixedCode) : Prop :=
  g.Valid binaryTypes unaryTypes ∧ g.underlying.PlanarValid

theorem planarValid_iff {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (h : g.Valid binaryTypes unaryTypes) :
    g.PlanarValid binaryTypes unaryTypes ↔ (g.toMultiGraph h).Planar := by
  rw [PlanarValid, and_iff_right h, GraphCode.planarValid_iff _ (g.underlying_valid h)]
  exact (g.underlyingIncidenceEquiv h).planar_iff.symm

/-- Binary-string promise for the unchanged mixed-code encoding. -/
def PlanarInput (binaryTypes unaryTypes : ℕ) (bits : Bits) : Prop :=
  ∃ g : MixedCode, encoding.decode bits = some g ∧ g.PlanarValid binaryTypes unaryTypes

@[simp] theorem planarInput_encode_iff (binaryTypes unaryTypes : ℕ) (g : MixedCode) :
    PlanarInput binaryTypes unaryTypes (encoding.encode g) ↔
      g.PlanarValid binaryTypes unaryTypes := by
  simp [PlanarInput, encoding.decode_encode]

end PlanarHom.Complexity.MixedCode
