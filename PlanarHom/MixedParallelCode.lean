import PlanarHom.GraphParallelSemantics
import PlanarHom.ListCodecMachines

/-! Exact selected-label occurrence replication and its raw finite-parser oracle. -/

namespace PlanarHom.Complexity

/-- Discard one escaped word, with an explicit empty fallback on malformed input. -/
def skipFrame : Bits → Bits
  | false::bs => bs
  | true::_::bs => skipFrame bs
  | _ => []

@[simp] theorem skipFrame_frame_append (word tail : Bits) :
    skipFrame (BitEncoding.frame word++tail) = tail := by
  induction word <;> simp_all [BitEncoding.frame,skipFrame]

/-- An edge's third coordinate follows its two framed endpoint words. -/
def labelMatches (selected : ℕ) (word : Bits) : Bool :=
  skipFrame (skipFrame word) == BitEncoding.nat.encode selected

/-- One total bit-string oracle supports both exact successor and fixed-label
classification. Tags are part of the materialized, charged query string. -/
def selectedOracle (selected : ℕ) : Bits → Bits
  | [] => []
  | false::xs => PlanarHom.BinaryArithmetic.succBits xs
  | true::xs => [labelMatches selected xs]

@[simp] theorem selectedOracle_succ (selected n : ℕ) :
    selectedOracle selected (false::BitEncoding.nat.encode n) = BitEncoding.nat.encode (n+1) :=
  PlanarHom.BinaryArithmetic.succBits_encodeNat n

@[simp] theorem labelMatches_edge (selected : ℕ) (e : ℕ × (ℕ × ℕ)) :
    labelMatches selected ((BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode e) =
      decide (e.2.2 = selected) := by
  apply Bool.eq_iff_iff.mpr
  simp only [labelMatches,BitEncoding.prod,skipFrame_frame_append,beq_iff_eq,decide_eq_true_eq]
  exact BitEncoding.nat.injective.eq_iff

/-- Each selected occurrence becomes `s` copies in place; all other entries
remain single occurrences in their original relative order. -/
def repeatSelected {α : Type} (test : α → Bool) (s : ℕ) (xs : List α) : List α :=
  xs.flatMap (fun x=>if test x then List.replicate s x else [x])

@[simp] theorem repeatSelected_nil {α : Type} (test : α → Bool) (s : ℕ) :
    repeatSelected test s ([] : List α) = [] := rfl

@[simp] theorem repeatSelected_cons {α : Type} (test : α → Bool) (s : ℕ) (x : α) (xs : List α) :
    repeatSelected test s (x::xs) =
      (if test x then List.replicate s x else [x])++repeatSelected test s xs := by
  simp [repeatSelected]

theorem repeatSelected_mem {α : Type} (test : α → Bool) (s : ℕ) (xs : List α) {x : α}
    (hx : x ∈ repeatSelected test s xs) : x ∈ xs := by
  obtain ⟨y,hy,hxy⟩ := List.mem_flatMap.mp hx
  split at hxy
  · have he := (List.mem_replicate.mp hxy).2
    simpa only [he] using hy
  · have he := List.mem_singleton.mp hxy
    simpa only [he] using hy

/-- A polynomial-size bound also covers zero replication and unmatched labels. -/
theorem repeatSelected_length_le {α : Type} (test : α → Bool) (s : ℕ) (xs : List α) :
    (repeatSelected test s xs).length ≤ (s+1)*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : test x <;> simp [repeatSelected_cons,h,Nat.mul_add] <;> omega

namespace MixedCode

/-- Thicken only the specified binary label. Unary occurrences and vertices are
unchanged exactly, including their serialized order and multiplicity. -/
def parallelLabel (selected s : ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,repeatSelected (fun e=>decide (e.2.2=selected)) s g.edges,g.unaries⟩

@[simp] theorem parallelLabel_vertices (selected s : ℕ) (g : MixedCode) :
    (parallelLabel selected s g).vertices = g.vertices := rfl
@[simp] theorem parallelLabel_unaries (selected s : ℕ) (g : MixedCode) :
    (parallelLabel selected s g).unaries = g.unaries := rfl

theorem parallelLabel_valid (selected s binaryTypes unaryTypes : ℕ) (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) : (g.parallelLabel selected s).Valid binaryTypes unaryTypes := by
  constructor
  · intro e he
    exact hg.1 e (repeatSelected_mem _ _ _ he)
  · exact hg.2

/-- The unchanged unary payload retains its own original length header; only
the binary occurrence-list header is recomputed. -/
theorem parallelLabel_encoding (selected s : ℕ) (g : MixedCode) :
    encoding.encode (parallelLabel selected s g) =
      BitEncoding.frame (BitEncoding.unaryNat.encode g.vertices) ++
      BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode (parallelLabel selected s g).edges.length) ++
        BitEncoding.frames ((parallelLabel selected s g).edges.map
          (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).encode)) ++
      unaryEncoding.encode g.unaries := by
  simp [encoding,BitEncoding.retract,BitEncoding.prod,BitEncoding.list,parallelLabel,unaryEncoding,
    List.append_assoc]

end MixedCode
end PlanarHom.Complexity
