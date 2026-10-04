import PlanarHom.Complexity

/-! Explicit occurrence-count size bounds for the existing binary codecs. -/

namespace PlanarHom.Complexity
namespace MixedCode

/-- Every vertex, binary occurrence, and unary occurrence is charged by the
actual mixed input encoding. Labels and endpoint values do not hide multiplicity. -/
theorem size_le_length (g : MixedCode) :
    g.vertices+g.edges.length+g.unaries.length ≤ (encoding.encode g).length := by
  have he := (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).list_length_le g.edges
  have hu := (BitEncoding.nat.prod BitEncoding.nat).list_length_le g.unaries
  simp only [encoding,BitEncoding.retract,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  omega

theorem vertices_le_length (g : MixedCode) : g.vertices≤(encoding.encode g).length := by
  have h:=size_le_length g; omega

theorem edges_le_length (g : MixedCode) : g.edges.length≤(encoding.encode g).length := by
  have h:=size_le_length g; omega

theorem unaries_le_length (g : MixedCode) : g.unaries.length≤(encoding.encode g).length := by
  have h:=size_le_length g; omega

end MixedCode
end PlanarHom.Complexity
