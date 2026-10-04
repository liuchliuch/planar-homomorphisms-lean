import PlanarHom.PlanarGraphCode
import PlanarHom.PlanarStretch
import PlanarHom.PlanarTransport
import PlanarHom.GraphParallelCode
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Concrete edge stretching on the ordinary serialized graph code

`GraphCode.stretch n` is a total raw-code transformation. It emits `n + 1`
segments per edge occurrence and allocates `n` private vertices per occurrence.
Endpoint validity, occurrence counts, incidence reindexing and ordinary planarity
are proved separately. No planarity certificate is added to the input, and the
existence of this Lean function does not assert a polynomial-time machine.
-/

namespace PlanarHom.Complexity.GraphCode

/-- Code of the `k`th private vertex of old edge occurrence `e`. -/
def stretchInternal (g : GraphCode) (n : ℕ) (e : Fin g.edges.length) (k : Fin n) : ℕ :=
  g.vertices + (finProdFinEquiv (e,k)).val

theorem stretchInternal_lt (g : GraphCode) (n : ℕ) (e : Fin g.edges.length) (k : Fin n) :
    g.stretchInternal n e k < g.vertices + g.edges.length * n :=
  Nat.add_lt_add_left (finProdFinEquiv (e,k)).isLt _

/-- Ordered endpoints of one emitted path segment. The test refers to the segment
index, not to whether the original endpoint pair happens to be a loop. -/
def stretchEndpoints (g : GraphCode) (n : ℕ) (p : Fin g.edges.length × Fin (n+1)) : ℕ × ℕ :=
  (if h : p.2.val = 0 then (g.edges.get p.1).1
    else g.stretchInternal n p.1 ⟨p.2.val - 1, by omega⟩,
   if h : p.2.val = n then (g.edges.get p.1).2
    else g.stretchInternal n p.1 ⟨p.2.val, by omega⟩)

/-- Concrete graph-code stretching; the vertex header still uses the existing
unary codec and the endpoint pairs still use the existing binary codec. -/
def stretch (g : GraphCode) (n : ℕ) : GraphCode where
  vertices := g.vertices + g.edges.length * n
  edges := List.ofFn (fun q : Fin (g.edges.length * (n+1)) =>
    g.stretchEndpoints n (finProdFinEquiv.symm q))

@[simp] theorem stretch_vertices (g : GraphCode) (n : ℕ) :
    (g.stretch n).vertices = g.vertices + g.edges.length * n := rfl

@[simp] theorem stretch_edges_length (g : GraphCode) (n : ℕ) :
    (g.stretch n).edges.length = g.edges.length * (n+1) := by simp [stretch]

theorem stretchEndpoints_valid (g : GraphCode) (hg : g.Valid) (n : ℕ)
    (p : Fin g.edges.length × Fin (n+1)) :
    (g.stretchEndpoints n p).1 < (g.stretch n).vertices ∧
    (g.stretchEndpoints n p).2 < (g.stretch n).vertices := by
  have he := hg (g.edges.get p.1) (List.get_mem _ _)
  constructor
  · dsimp [stretchEndpoints]
    split
    · exact he.1.trans_le (Nat.le_add_right _ _)
    · exact g.stretchInternal_lt n p.1 _
  · dsimp [stretchEndpoints]
    split
    · exact he.2.trans_le (Nat.le_add_right _ _)
    · exact g.stretchInternal_lt n p.1 _

/-- Every emitted endpoint stays within the new unary vertex header. -/
theorem stretch_valid (g : GraphCode) (hg : g.Valid) (n : ℕ) : (g.stretch n).Valid := by
  intro e he
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp he
  exact g.stretchEndpoints_valid hg n _

/-- Explicit bijection on all old and newly allocated vertices. -/
def stretchVertexEquiv (g : GraphCode) (n : ℕ) :
    Fin g.vertices ⊕ (Fin g.edges.length × Fin n) ≃ Fin (g.stretch n).vertices :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

/-- Explicit bijection on path-segment occurrences and output list positions. -/
def stretchEdgeEquiv (g : GraphCode) (n : ℕ) :
    (Fin g.edges.length × Fin (n+1)) ≃ Fin (g.stretch n).edges.length :=
  finProdFinEquiv.trans (finCongr (g.stretch_edges_length n).symm)

@[simp] theorem stretch_get (g : GraphCode) (n : ℕ)
    (p : Fin g.edges.length × Fin (n+1)) :
    (g.stretch n).edges.get (g.stretchEdgeEquiv n p) = g.stretchEndpoints n p := by
  simp only [stretch, stretchEdgeEquiv, Equiv.trans_apply, List.get_eq_getElem, List.getElem_ofFn]
  change g.stretchEndpoints n (finProdFinEquiv.symm (finProdFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

/-- The raw-code output is exactly the already defined topological stretching,
up to the explicitly proved vertex and occurrence-edge bijections. -/
def stretchIncidenceEquiv (g : GraphCode) (hg : g.Valid) (n : ℕ) :
    MultiGraph.IncidenceEquiv ((g.toMultiGraph hg).stretch n)
      ((g.stretch n).toMultiGraph (g.stretch_valid hg n)) where
  vertex := g.stretchVertexEquiv n
  edge := g.stretchEdgeEquiv n
  src_eq p := by
    apply Fin.ext
    change ((g.stretch n).edges.get (g.stretchEdgeEquiv n p)).1 = _
    rw [stretch_get]
    by_cases hk : p.2.val = 0
    · simp [stretchEndpoints, MultiGraph.stretch, MultiGraph.stretchSrc, hk,
        stretchVertexEquiv, toMultiGraph]
    · simp [stretchEndpoints, MultiGraph.stretch, MultiGraph.stretchSrc, hk,
        stretchVertexEquiv, stretchInternal]
  dst_eq p := by
    apply Fin.ext
    change ((g.stretch n).edges.get (g.stretchEdgeEquiv n p)).2 = _
    rw [stretch_get]
    by_cases hk : p.2.val = n
    · simp [stretchEndpoints, MultiGraph.stretch, MultiGraph.stretchDst, hk,
        stretchVertexEquiv, toMultiGraph]
    · simp [stretchEndpoints, MultiGraph.stretch, MultiGraph.stretchDst, hk,
        stretchVertexEquiv, stretchInternal]

/-- Planarity preservation for actual raw graph-code inputs, with no embedded-
input restriction and no planarity-recognition hypothesis. -/
theorem PlanarValid.stretch {g : GraphCode} (h : g.PlanarValid) (n : ℕ) :
    (g.stretch n).PlanarValid := by
  obtain ⟨hg,hp⟩ := h
  refine ⟨g.stretch_valid hg n, ?_⟩
  exact (g.stretchIncidenceEquiv hg n).planar_iff.mp (hp.stretch n)

/-- Numeric serialization bound for any endpoint-valid occurrence list.
This deliberately uses a loose linear bound on each binary natural codeword. -/
theorem edgeFrames_length_le (vertices : ℕ) (edges : List (ℕ × ℕ))
    (h : ∀ e ∈ edges, e.1 < vertices ∧ e.2 < vertices) :
    (BitEncoding.frames (edges.map (BitEncoding.nat.prod BitEncoding.nat).encode)).length ≤
      edges.length * (6 * vertices + 3) := by
  induction edges with
  | nil => simp [BitEncoding.frames]
  | cons e es ih =>
    have he := h e (by simp)
    have hs := ih (fun a ha => h a (by simp [ha]))
    have h₁ := encodeNat_length_le e.1
    have h₂ := encodeNat_length_le e.2
    have hf : (BitEncoding.frame ((BitEncoding.nat.prod BitEncoding.nat).encode e)).length ≤
        6 * vertices + 3 := by
      simp only [BitEncoding.frame_length, BitEncoding.prod_length]
      omega
    simp only [List.map_cons, BitEncoding.frames, List.length_append, List.length_cons]
    nlinarith

/-- An explicit bit-length bound for the existing unary-header/binary-endpoint
codec. It applies to the output without changing its serialization. -/
theorem encoding_length_le_of_valid (g : GraphCode) (hg : g.Valid) :
    (encoding.encode g).length ≤
      2 * g.vertices + g.edges.length * (6 * g.vertices + 5) + 2 := by
  have hf := edgeFrames_length_le g.vertices g.edges hg
  have hm := encodeNat_length_le g.edges.length
  simp only [encoding, BitEncoding.retract, BitEncoding.prod_length,
    BitEncoding.unaryNat_length, BitEncoding.list, List.length_append, BitEncoding.frame_length]
  nlinarith

/-- Exact occurrence counts substituted into the ordinary codec bound. -/
theorem stretch_encoding_length_le (g : GraphCode) (hg : g.Valid) (n : ℕ) :
    (encoding.encode (g.stretch n)).length ≤
      2 * (g.vertices + g.edges.length * n) +
        (g.edges.length * (n+1)) * (6 * (g.vertices + g.edges.length * n) + 5) + 2 := by
  simpa only [stretch_vertices, stretch_edges_length] using
    encoding_length_le_of_valid (g.stretch n) (g.stretch_valid hg n)

/-- A polynomial bound in the original bit length and the numeric stretch
parameter. This is an output-size theorem, not an FP implementation theorem. -/
theorem stretch_encoding_length_polynomial (g : GraphCode) (hg : g.Valid) (n : ℕ) :
    (encoding.encode (g.stretch n)).length ≤
      6 * ((n+1) * (encoding.encode g).length)^2 +
        7 * ((n+1) * (encoding.encode g).length) + 2 := by
  let L := (encoding.encode g).length
  let B := (n+1) * L
  have hsize := g.size_le_length
  have hv : g.vertices ≤ L := by dsimp [L]; omega
  have he : g.edges.length ≤ L := by dsimp [L]; omega
  have hV : g.vertices + g.edges.length * n ≤ B := by
    calc
      _ ≤ L + L*n := Nat.add_le_add hv (Nat.mul_le_mul_right n he)
      _ = B := by dsimp [B]; ring
  have hE : g.edges.length * (n+1) ≤ B := by
    simpa only [B, Nat.mul_comm] using Nat.mul_le_mul_right (n+1) he
  have hprod := Nat.mul_le_mul hE (show 6 * (g.vertices + g.edges.length*n) + 5 ≤
      6*B+5 by omega)
  have hout := g.stretch_encoding_length_le hg n
  change (encoding.encode (g.stretch n)).length ≤ 6*B^2 + 7*B + 2
  nlinarith

end PlanarHom.Complexity.GraphCode
