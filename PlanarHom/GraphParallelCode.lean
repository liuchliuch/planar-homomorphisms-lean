import PlanarHom.BinaryArithmetic

/-! Exact occurrence replication and the serialized target of the graph compiler. -/

namespace PlanarHom.Complexity

open PlanarHom.BinaryArithmetic

/-- Replicate each occurrence in place. Equal entries remain separate occurrences. -/
def repeatWords {α : Type} (s : ℕ) (ws : List α) : List α := ws.flatMap (List.replicate s)

@[simp] theorem repeatWords_nil {α : Type} (s : ℕ) : repeatWords s ([] : List α) = [] := rfl
@[simp] theorem repeatWords_cons {α : Type} (s : ℕ) (w : α) (ws : List α) :
    repeatWords s (w::ws) = List.replicate s w ++ repeatWords s ws := by simp [repeatWords]

@[simp] theorem repeatWords_length {α : Type} (s : ℕ) (ws : List α) :
    (repeatWords s ws).length = s*ws.length := by
  induction ws <;> simp_all [Nat.mul_add,Nat.add_comm]

theorem repeatWords_map {α β : Type} (f : α → β) (s : ℕ) (ws : List α) :
    (repeatWords s ws).map f = repeatWords s (ws.map f) := by
  induction ws <;> simp_all [repeatWords_cons]

@[simp] theorem frames_append (a b : List Bits) :
    BitEncoding.frames (a++b) = BitEncoding.frames a ++ BitEncoding.frames b := by
  induction a <;> simp_all [BitEncoding.frames,List.append_assoc]

/-- One fixed word repeated as a literal framed bit payload. -/
def repeatFrame (s : ℕ) (w : Bits) : Bits := BitEncoding.frames (List.replicate s w)

@[simp] theorem repeatFrame_zero (w : Bits) : repeatFrame 0 w = [] := rfl
@[simp] theorem repeatFrame_succ (s : ℕ) (w : Bits) :
    repeatFrame (s+1) w = BitEncoding.frame w ++ repeatFrame s w := by
  simp [repeatFrame,BitEncoding.frames,List.replicate_succ]

@[simp] theorem repeatFrame_length (s : ℕ) (w : Bits) :
    (repeatFrame s w).length = s*(BitEncoding.frame w).length := by
  induction s <;> simp_all [Nat.add_mul,Nat.add_comm]

@[simp] theorem frames_repeatWords_cons (s : ℕ) (w : Bits) (ws : List Bits) :
    BitEncoding.frames (repeatWords s (w::ws)) =
      repeatFrame s w ++ BitEncoding.frames (repeatWords s ws) := by
  simp [repeatFrame]

@[simp] theorem frames_repeatWords_length (s : ℕ) (ws : List Bits) :
    (BitEncoding.frames (repeatWords s ws)).length = s*(BitEncoding.frames ws).length := by
  induction ws with
  | nil => simp [BitEncoding.frames]
  | cons w ws ih =>
    rw [frames_repeatWords_cons,List.length_append,repeatFrame_length,ih]
    simp only [BitEncoding.frames,List.length_append,Nat.mul_add]

/-- A loose numeric bound, used only after the emitted occurrence count is
bounded polynomially by the explicit unary multiplier and graph size. -/
theorem encodeNat_length_le (n : ℕ) : (BitEncoding.nat.encode n).length ≤ n := by
  induction n with
  | zero => simp [BitEncoding.nat,Computability.encodeNat,Computability.encodeNum]
  | succ n ih =>
    have h := succBits_length_le (BitEncoding.nat.encode n)
    rw [show succBits (BitEncoding.nat.encode n) = BitEncoding.nat.encode (n+1)
      from succBits_encodeNat n] at h
    omega

namespace GraphCode

/-- Replace every edge occurrence by `s` copies, preserving its endpoints. -/
def parallel (s : ℕ) (g : GraphCode) : GraphCode := ⟨g.vertices,repeatWords s g.edges⟩

@[simp] theorem parallel_vertices (s : ℕ) (g : GraphCode) : (parallel s g).vertices = g.vertices := rfl
@[simp] theorem parallel_edges_length (s : ℕ) (g : GraphCode) :
    (parallel s g).edges.length = s*g.edges.length := repeatWords_length s g.edges

theorem parallel_valid (s : ℕ) (g : GraphCode) (hg : g.Valid) : (parallel s g).Valid := by
  intro e he
  obtain ⟨e',he',herep⟩ := List.mem_flatMap.mp he
  have heq : e = e' := (List.mem_replicate.mp herep).2
  exact heq ▸ hg e' he'

/-- The output header is the canonical binary product of the multiplier and
original number of edge occurrences; every occurrence retains its exact codeword. -/
theorem parallel_encoding (s : ℕ) (g : GraphCode) :
    encoding.encode (parallel s g) =
      BitEncoding.frame (BitEncoding.unaryNat.encode g.vertices) ++
      BitEncoding.frame (BitEncoding.nat.encode (s*g.edges.length)) ++
      BitEncoding.frames (repeatWords s (g.edges.map (BitEncoding.nat.prod BitEncoding.nat).encode)) := by
  simp [encoding,BitEncoding.retract,BitEncoding.prod,BitEncoding.list,parallel,
    repeatWords_length,repeatWords_map,List.append_assoc]

end GraphCode
end PlanarHom.Complexity
