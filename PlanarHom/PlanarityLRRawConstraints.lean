import PlanarHom.PlanarityLRConstraintBlocks
import PlanarHom.PlanarityDepthFirstSearchProgram

/-!
# NEW literal LR fork extraction from the actual raw-code DFS

All quantities below are executable functions of the ordinary mixed graph code.
No forest, side assignment, embedding, rotation or face table is input data.
Correctness here identifies the exact computed fork condition; the topological
LR characterization is deliberately not assumed or claimed.
-/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PlanarityDepthFirstSearch PlanarityLRConstraintBlocks PlanarityParitySolver

def edge (g : MixedCode) (e : ℕ) : ℕ × (ℕ × ℕ) := g.edges.getD e (0,0,0)

def lower (g : MixedCode) (e : ℕ) : ℕ :=
  if height g (edge g e).1 ≤ height g (edge g e).2.1 then (edge g e).1 else (edge g e).2.1

def upper (g : MixedCode) (e : ℕ) : ℕ :=
  if height g (edge g e).1 ≤ height g (edge g e).2.1 then (edge g e).2.1 else (edge g e).1

def isTree (g : MixedCode) (e : ℕ) : Bool :=
  decide (e < g.edges.length ∧ 0 < height g (upper g e) ∧ parentEdge g (upper g e) = e)

def source (g : MixedCode) (e : ℕ) : ℕ := if isTree g e then lower g e else upper g e

def target (g : MixedCode) (e : ℕ) : ℕ := if isTree g e then upper g e else lower g e

def isBack (g : MixedCode) (e : ℕ) : Bool :=
  decide (e < g.edges.length ∧ isTree g e = false ∧ source g e ≠ target g e)

def targetHeight (g : MixedCode) (e : ℕ) : ℕ := height g (target g e)

/-- Reflexive ancestor membership in the literal saved DFS path. -/
def ancestor (g : MixedCode) (u v : ℕ) : Bool := decide (u = v ∨ u ∈ ancestors g v)

/-- Return-edge occurrences retain their original labels; loops are excluded. -/
def returns (g : MixedCode) (e : ℕ) : List ℕ :=
  if isTree g e then
    (List.range g.edges.length).filter (fun b => isBack g b &&
      ancestor g (target g e) (source g b) && decide (targetHeight g b < height g (source g e)))
  else if isBack g e then [e] else []

/-- The source-depth fallback is exact when no return exists. -/
def lowpoint (g : MixedCode) (e : ℕ) : ℕ :=
  ((returns g e).map (targetHeight g)).foldl min (height g (source g e))

def outgoing (g : MixedCode) (v : ℕ) : List ℕ :=
  (List.range g.edges.length).filter (fun e =>
    (isTree g e || isBack g e) && decide (source g e = v))

def forkBlock (g : MixedCode) (e₁ e₂ : ℕ) : ForkBlock :=
  ((returns g e₁).filter (fun b => decide (lowpoint g e₂ < targetHeight g b)),
   (returns g e₂).filter (fun b => decide (lowpoint g e₁ < targetHeight g b)))

/-- Both orders of a distinct outgoing pair are harmlessly retained. -/
def forkBlocks (g : MixedCode) : List ForkBlock :=
  (List.range g.vertices).flatMap (fun v => if height g v = 0 then [] else
    (outgoing g v).flatMap (fun e₁ =>
      ((outgoing g v).filter (fun e₂ => decide (e₂ ≠ e₁))).map (forkBlock g e₁)))

def LRCondition (g : MixedCode) (side : ℕ → Bool) : Prop :=
  ∀ v < g.vertices, 0 < height g v → ∀ e₁ ∈ outgoing g v, ∀ e₂ ∈ outgoing g v,
    e₂ ≠ e₁ → ForkHolds side (forkBlock g e₁ e₂)

def solveLR (g : MixedCode) : Bool × Assignment := decideBlocks (forkBlocks g)

theorem returns_valid (g : MixedCode) (e : ℕ) {b : ℕ} (hb : b ∈ returns g e) : b < g.edges.length := by
  unfold returns at hb
  split_ifs at hb with ht he
  · exact List.mem_range.mp (List.mem_filter.mp hb).1
  · have hh : b = e := by simpa using hb
    subst b
    exact (of_decide_eq_true he).1
  · simp at hb

theorem outgoing_valid (g : MixedCode) (v : ℕ) {e : ℕ} (he : e ∈ outgoing g v) : e < g.edges.length :=
  List.mem_range.mp (List.mem_filter.mp he).1

theorem returns_length (g : MixedCode) (e : ℕ) : (returns g e).length ≤ g.edges.length := by
  unfold returns
  split_ifs with ht he
  · simpa using List.length_filter_le
      (fun b => isBack g b && ancestor g (target g e) (source g b) &&
        decide (targetHeight g b < height g (source g e))) (List.range g.edges.length)
  · have hh := (of_decide_eq_true he).1
    simp
    omega
  · simp

theorem outgoing_length (g : MixedCode) (v : ℕ) : (outgoing g v).length ≤ g.edges.length := by
  unfold outgoing
  simpa using List.length_filter_le
    (fun e => (isTree g e || isBack g e) && decide (source g e = v)) (List.range g.edges.length)

/-- Exact characterization of every generated block, including the incoming-tree
requirement (positive vertex depth) and distinct outgoing occurrences. -/
theorem mem_forkBlocks (g : MixedCode) (B : ForkBlock) : B ∈ forkBlocks g ↔
    ∃ v, v < g.vertices ∧ 0 < height g v ∧
      ∃ e₁ ∈ outgoing g v, ∃ e₂ ∈ outgoing g v, e₂ ≠ e₁ ∧ forkBlock g e₁ e₂ = B := by
  constructor
  · intro h
    obtain ⟨v,hv,h⟩ := List.mem_flatMap.mp h
    have hv' := List.mem_range.mp hv
    split_ifs at h with hz
    · simp at h
    · obtain ⟨e₁,he₁,h⟩ := List.mem_flatMap.mp h
      obtain ⟨e₂,he₂,heq⟩ := List.mem_map.mp h
      have hh := List.mem_filter.mp he₂
      exact ⟨v,hv',Nat.pos_of_ne_zero hz,e₁,he₁,e₂,hh.1,of_decide_eq_true hh.2,heq⟩
  · rintro ⟨v,hv,hheight,e₁,he₁,e₂,he₂,hne,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨v,List.mem_range.mpr hv,?_⟩
    rw [if_neg (Nat.ne_of_gt hheight)]
    exact List.mem_flatMap.mpr ⟨e₁,he₁,List.mem_map.mpr
      ⟨e₂,List.mem_filter.mpr ⟨he₂,decide_eq_true hne⟩,rfl⟩⟩

theorem forkBlocks_spec (g : MixedCode) (side : ℕ → Bool) :
    LRPartition side (forkBlocks g) ↔ LRCondition g side := by
  constructor
  · intro h v hv hheight e₁ he₁ e₂ he₂ hne
    exact h _ ((mem_forkBlocks g _).mpr ⟨v,hv,hheight,e₁,he₁,e₂,he₂,hne,rfl⟩)
  · intro h B hB
    obtain ⟨v,hv,hheight,e₁,he₁,e₂,he₂,hne,rfl⟩ := (mem_forkBlocks g B).mp hB
    exact h v hv hheight e₁ he₁ e₂ he₂ hne

/-- The actual raw-code computation returns a valid solution of all its LR forks. -/
theorem solveLR_sound (g : MixedCode) (h : (solveLR g).1 = true) :
    LRCondition g (lookup (solveLR g).2) :=
  (forkBlocks_spec g _).mp (decideBlocks_sound _ h)

/-- Exact completeness for the combinatorial condition, without assuming or
identifying it with topological planarity. -/
theorem solveLR_complete (g : MixedCode) :
    (solveLR g).1 = true ↔ ∃ side, LRCondition g side := by
  rw [solveLR,decideBlocks_complete]
  exact exists_congr (fun side => forkBlocks_spec g side)



/-- Each extracted side has at most one entry per original occurrence. -/
theorem forkBlock_lengths (g : MixedCode) (e₁ e₂ : ℕ) :
    (forkBlock g e₁ e₂).1.length ≤ g.edges.length ∧
      (forkBlock g e₁ e₂).2.length ≤ g.edges.length := by
  exact ⟨(List.length_filter_le _ _).trans (returns_length g e₁),
    (List.length_filter_le _ _).trans (returns_length g e₂)⟩

/-- Literal ordered-fork enumeration has a cubic combinatorial output bound. -/
theorem forkBlocks_length (g : MixedCode) :
    (forkBlocks g).length ≤ g.vertices*g.edges.length^2 := by
  unfold forkBlocks
  rw [List.length_flatMap]
  apply (ListMapMachines.sum_map_le_mul _ (List.range g.vertices) (g.edges.length^2) ?_).trans
  · simp [Nat.mul_comm]
  · intro v _
    split_ifs with hv
    · simp
    · rw [List.length_flatMap]
      have hl := outgoing_length g v
      have hs := ListMapMachines.sum_map_le_mul
        (fun e₁ => (((outgoing g v).filter (fun e₂ => decide (e₂ ≠ e₁))).map (forkBlock g e₁)).length)
        (outgoing g v) g.edges.length (by
          intro e he
          simp only [List.length_map]
          exact (List.length_filter_le _ _).trans hl)
      simpa only [pow_two] using hs.trans (Nat.mul_le_mul_right g.edges.length hl)

/-- The complete literal pairwise system is still polynomial in raw graph counts. -/
theorem compiled_forks_length (g : MixedCode) :
    (compile (forkBlocks g)).length ≤ 3*g.vertices*g.edges.length^4 := by
  unfold compile
  rw [List.length_flatMap]
  have hblock : ∀ B ∈ forkBlocks g, (equations B).length ≤ 3*g.edges.length^2 := by
    intro B hB
    obtain ⟨v,hv,hh,e₁,he₁,e₂,he₂,hne,rfl⟩ := (mem_forkBlocks g B).mp hB
    have hs := forkBlock_lengths g e₁ e₂
    rw [equations_length]
    have h₁ := Nat.mul_le_mul hs.1 hs.1
    have h₂ := Nat.mul_le_mul hs.2 hs.2
    have h₃ := Nat.mul_le_mul hs.1 hs.2
    nlinarith
  have hs := ListMapMachines.sum_map_le_mul (fun B => (equations B).length)
    (forkBlocks g) (3*g.edges.length^2) hblock
  have hh := Nat.mul_le_mul_left (3*g.edges.length^2) (forkBlocks_length g)
  calc
    _ ≤ (3*g.edges.length^2)*(forkBlocks g).length := by simpa only [Nat.mul_comm] using hs
    _ ≤ (3*g.edges.length^2)*(g.vertices*g.edges.length^2) := hh
    _ = _ := by ring

end PlanarHom.PlanarityLRRawConstraints
