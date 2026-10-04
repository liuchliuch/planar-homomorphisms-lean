import PlanarHom.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Exact two-terminal gadget semantics

A gadget is a finite multigraph with two distinct tagged terminals and a finite
set of internal vertices. Its signature sums over internal colors and includes
background weights only at internal vertices. The series operation turns the
identified terminals into one internal vertex, so its weight is included once.
Parallel edges and loops are retained by explicit edge labels.

These are algebraic identities for finite multigraphs. No planar embedding,
planarity-preservation theorem, or complexity reduction is asserted here.
-/

open scoped BigOperators
open Classical

noncomputable section

namespace PlanarHom

/-- The two terminals are `Sum.inl false` and `Sum.inl true`. -/
abbrev TwoTerminal (I E : Type*) := MultiGraph (Bool ⊕ I) E

namespace TwoTerminal

local instance (priority := 10000) (α : Type*) : DecidableEq α := Classical.decEq α

variable {I J E F C R : Type*}
variable [Fintype I] [Fintype J] [Fintype E] [Fintype F]
variable [Fintype C] [CommSemiring R]

/-- Extend internal colors by fixed left and right terminal colors. -/
def extend (i j : C) (σ : I → C) : Bool ⊕ I → C :=
  Sum.elim (fun b => cond b j i) σ

/-- Edge contribution, with multiplicity and loops represented by edge labels. -/
def edgeWeight (G : TwoTerminal I E) (M : Matrix C C R)
    (i j : C) (σ : I → C) : R :=
  ∏ e, M (extend i j σ (G.src e)) (extend i j σ (G.dst e))

/-- A pinned assignment includes internal background weights, but no terminal
background weights. -/
def assignmentWeight (G : TwoTerminal I E) (M : Matrix C C R) (w : C → R)
    (i j : C) (σ : I → C) : R :=
  (∏ v, w (σ v)) * edgeWeight G M i j σ

/-- The interaction realized by a two-terminal gadget. -/
def signature (G : TwoTerminal I E) (M : Matrix C C R) (w : C → R) : Matrix C C R :=
  fun i j => ∑ σ : I → C, assignmentWeight G M w i j σ

/-- One edge, with no internal vertices. -/
def singleEdge : TwoTerminal Empty PUnit :=
  ⟨fun _ => Sum.inl false, fun _ => Sum.inl true⟩

@[simp] theorem signature_singleEdge (M : Matrix C C R) (w : C → R) :
    signature singleEdge M w = M := by
  funext i j
  simp [signature, assignmentWeight, edgeWeight, singleEdge, extend]

/-- `n` distinct parallel edge labels on the same two terminals. -/
def parallelEdges (n : ℕ) : TwoTerminal Empty (Fin n) :=
  ⟨fun _ => Sum.inl false, fun _ => Sum.inl true⟩

/-- Parallel edge copies realize an entrywise power, including `n = 0`. -/
@[simp] theorem signature_parallelEdges (n : ℕ) (M : Matrix C C R) (w : C → R) :
    signature (parallelEdges n) M w = fun i j => (M i j) ^ n := by
  funext i j
  simp [signature, assignmentWeight, edgeWeight, parallelEdges, extend]

/-- The two-edge path has one internal vertex. -/
def twoEdgePath : TwoTerminal PUnit Bool where
  src := fun b => cond b (Sum.inr PUnit.unit) (Sum.inl false)
  dst := fun b => cond b (Sum.inl true) (Sum.inr PUnit.unit)

/-- The middle vertex contributes its background weight exactly once. -/
theorem signature_twoEdgePath (M : Matrix C C R) (w : C → R) (i j : C) :
    signature twoEdgePath M w i j = ∑ k, M i k * w k * M k j := by
  unfold signature
  apply Fintype.sum_equiv (Equiv.funUnique PUnit C)
  intro σ
  simp [assignmentWeight, edgeWeight, twoEdgePath, extend,
    Equiv.funUnique, Equiv.piUnique]
  ac_rfl

/-- Matrix form of the weighted two-edge path identity: `M D M`. -/
theorem signature_twoEdgePath_matrix (M : Matrix C C R) (w : C → R) :
    signature twoEdgePath M w = M * Matrix.diagonal w * M := by
  funext i j
  rw [signature_twoEdgePath, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

/-- At unit background the two-edge path realizes the ordinary square. -/
theorem signature_twoEdgePath_one (M : Matrix C C R) :
    signature twoEdgePath M (fun _ => 1) = M * M := by
  funext i j
  simp [signature_twoEdgePath, Matrix.mul_apply]

/-- Split a sum over assignments on tagged disjoint internal vertex sets. -/
theorem sum_colorings_sum (f : (I ⊕ J → C) → R) :
    (∑ σ : I ⊕ J → C, f σ) =
      ∑ σ : I → C, ∑ τ : J → C, f (Sum.elim σ τ) := by
  calc
    _ = ∑ p : (I → C) × (J → C), f (Sum.elim p.1 p.2) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J C)
      intro σ
      congr 1
      funext x
      cases x <;> rfl
    _ = _ := Fintype.sum_prod_type _

/-- Split the colors of the two ordered terminals into two independent sums. -/
theorem sum_colorings_bool (f : (Bool → C) → R) :
    (∑ σ : Bool → C, f σ) = ∑ i : C, ∑ j : C, f (fun b => cond b j i) := by
  calc
    _ = ∑ p : C × C, f (fun b => cond b p.2 p.1) := by
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd C)
      intro σ
      congr 1
      funext b
      cases b <;> rfl
    _ = _ := Fintype.sum_prod_type _

omit [Fintype C] in
/-- Restoring the two omitted terminal weights gives the original multigraph
assignment contribution. -/
theorem fullAssignmentWeight_extend (G : TwoTerminal I E) (M : Matrix C C R)
    (w : C → R) (i j : C) (σ : I → C) :
    MultiGraph.assignmentWeight G M w (extend i j σ) =
      w i * w j * assignmentWeight G M w i j σ := by
  simp only [MultiGraph.assignmentWeight, assignmentWeight, edgeWeight,
    Fintype.prod_sum_type, extend, Sum.elim_inl, Sum.elim_inr, Fintype.prod_bool,
    Bool.cond_true, Bool.cond_false]
  ac_rfl

/-- Closing both terminals recovers the full partition function. This theorem
also pins down exactly which vertex weights the signature omits. -/
theorem partition_eq_sum_signature (G : TwoTerminal I E) (M : Matrix C C R) (w : C → R) :
    G.partition M w = ∑ i, ∑ j, w i * w j * signature G M w i j := by
  unfold MultiGraph.partition
  rw [sum_colorings_sum, sum_colorings_bool]
  change (∑ i, ∑ j, ∑ σ : I → C, MultiGraph.assignmentWeight G M w (extend i j σ)) = _
  simp only [fullAssignmentWeight_extend, signature, Finset.mul_sum]

/-- Include the left gadget's internal vertices in a parallel composition. -/
def parallelLeft : Bool ⊕ I → Bool ⊕ (I ⊕ J) :=
  Sum.map id Sum.inl

/-- Include the right gadget's internal vertices in a parallel composition. -/
def parallelRight : Bool ⊕ J → Bool ⊕ (I ⊕ J) :=
  Sum.map id Sum.inr

/-- Identify the corresponding terminals; keep internal vertices disjoint and
preserve each edge label, including any loops. -/
def parallel (G : TwoTerminal I E) (H : TwoTerminal J F) : TwoTerminal (I ⊕ J) (E ⊕ F) where
  src := Sum.elim (fun e => parallelLeft (G.src e)) (fun f => parallelRight (H.src f))
  dst := Sum.elim (fun e => parallelLeft (G.dst e)) (fun f => parallelRight (H.dst f))

omit [Fintype I] [Fintype J] [Fintype C] in
@[simp] theorem extend_parallelLeft (i j : C) (σ : I ⊕ J → C) (v : Bool ⊕ I) :
    extend i j σ (parallelLeft v) = extend i j (fun x => σ (Sum.inl x)) v := by
  cases v <;> rfl

omit [Fintype I] [Fintype J] [Fintype C] in
@[simp] theorem extend_parallelRight (i j : C) (σ : I ⊕ J → C) (v : Bool ⊕ J) :
    extend i j σ (parallelRight v) = extend i j (fun x => σ (Sum.inr x)) v := by
  cases v <;> rfl

omit [Fintype C] in
/-- Assignment-level factorization for parallel composition. -/
theorem assignmentWeight_parallel (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) (w : C → R) (i j : C) (σ : I ⊕ J → C) :
    assignmentWeight (parallel G H) M w i j σ =
      assignmentWeight G M w i j (fun x => σ (Sum.inl x)) *
      assignmentWeight H M w i j (fun x => σ (Sum.inr x)) := by
  simp only [assignmentWeight, edgeWeight, Fintype.prod_sum_type, parallel,
    Sum.elim_inl, Sum.elim_inr, extend_parallelLeft, extend_parallelRight]
  ac_rfl

/-- Parallel composition realizes the entrywise (Hadamard) product. -/
theorem signature_parallel (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) (w : C → R) (i j : C) :
    signature (parallel G H) M w i j = signature G M w i j * signature H M w i j := by
  simp only [signature, sum_colorings_sum, assignmentWeight_parallel,
    Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Embed the first gadget into a series composition. Its right terminal becomes
the new internal junction. -/
def seriesLeft : Bool ⊕ I → Bool ⊕ (PUnit ⊕ (I ⊕ J))
  | Sum.inl false => Sum.inl false
  | Sum.inl true => Sum.inr (Sum.inl PUnit.unit)
  | Sum.inr x => Sum.inr (Sum.inr (Sum.inl x))

/-- Embed the second gadget into a series composition. Its left terminal becomes
the same new internal junction. -/
def seriesRight : Bool ⊕ J → Bool ⊕ (PUnit ⊕ (I ⊕ J))
  | Sum.inl false => Sum.inr (Sum.inl PUnit.unit)
  | Sum.inl true => Sum.inl true
  | Sum.inr x => Sum.inr (Sum.inr (Sum.inr x))

/-- Glue the right terminal of the first gadget to the left terminal of the
second. The identified vertex is an internal vertex of the composite. -/
def series (G : TwoTerminal I E) (H : TwoTerminal J F) :
    TwoTerminal (PUnit ⊕ (I ⊕ J)) (E ⊕ F) where
  src := Sum.elim (fun e => seriesLeft (G.src e)) (fun f => seriesRight (H.src f))
  dst := Sum.elim (fun e => seriesLeft (G.dst e)) (fun f => seriesRight (H.dst f))

omit [Fintype I] [Fintype J] [Fintype C] in
@[simp] theorem extend_seriesLeft (i j : C) (σ : PUnit ⊕ (I ⊕ J) → C) (v : Bool ⊕ I) :
    extend i j σ (seriesLeft v) =
      extend i (σ (Sum.inl PUnit.unit)) (fun x => σ (Sum.inr (Sum.inl x))) v := by
  cases v with
  | inl b => cases b <;> rfl
  | inr x => rfl

omit [Fintype I] [Fintype J] [Fintype C] in
@[simp] theorem extend_seriesRight (i j : C) (σ : PUnit ⊕ (I ⊕ J) → C) (v : Bool ⊕ J) :
    extend i j σ (seriesRight v) =
      extend (σ (Sum.inl PUnit.unit)) j (fun x => σ (Sum.inr (Sum.inr x))) v := by
  cases v with
  | inl b => cases b <;> rfl
  | inr x => rfl

omit [Fintype C] in
/-- Series composition includes the weight of the glued vertex once. -/
theorem assignmentWeight_series (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) (w : C → R) (i j : C) (σ : PUnit ⊕ (I ⊕ J) → C) :
    assignmentWeight (series G H) M w i j σ =
      assignmentWeight G M w i (σ (Sum.inl PUnit.unit))
        (fun x => σ (Sum.inr (Sum.inl x))) * w (σ (Sum.inl PUnit.unit)) *
      assignmentWeight H M w (σ (Sum.inl PUnit.unit)) j
        (fun x => σ (Sum.inr (Sum.inr x))) := by
  simp only [assignmentWeight, edgeWeight, Fintype.prod_sum_type, series,
    Sum.elim_inl, Sum.elim_inr, extend_seriesLeft, extend_seriesRight,
    Fintype.prod_unique]
  ac_rfl

/-- General weighted series composition is the matrix product with the diagonal
background interaction between the two signatures. -/
theorem signature_series (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) (w : C → R) (i j : C) :
    signature (series G H) M w i j =
      ∑ k, signature G M w i k * w k * signature H M w k j := by
  unfold signature
  rw [sum_colorings_sum]
  calc
    _ = ∑ k : C, ∑ σ : I ⊕ J → C,
        assignmentWeight (series G H) M w i j (Sum.elim (fun _ => k) σ) := by
      apply Fintype.sum_equiv (Equiv.funUnique PUnit C)
      intro μ
      congr 1
    _ = _ := by
      simp only [sum_colorings_sum, assignmentWeight_series, Sum.elim_inl, Sum.elim_inr]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Matrix form of the exact series-composition rule. -/
theorem signature_series_matrix (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) (w : C → R) :
    signature (series G H) M w = signature G M w * Matrix.diagonal w * signature H M w := by
  funext i j
  rw [signature_series, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

/-- Ordinary matrix multiplication is recovered when all background weights are one. -/
theorem signature_series_one (G : TwoTerminal I E) (H : TwoTerminal J F)
    (M : Matrix C C R) :
    signature (series G H) M (fun _ => 1) =
      signature G M (fun _ => 1) * signature H M (fun _ => 1) := by
  funext i j
  simp [signature_series, Matrix.mul_apply]

end TwoTerminal
end PlanarHom
