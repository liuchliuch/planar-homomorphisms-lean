import PlanarHom.SelectedStretchSemantics
import PlanarHom.WeightedPathSemantics

/-! Actual selected edge stretching with original background weights at every
new private vertex. This is the weighted chain used by source3.7. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.Complexity.MixedCode
variable {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]

theorem stretch_vertex_weights (g : MixedCode) (selected replacement n : ℕ)
    (w : C → R) (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C) :
    (∏ v, w (g.stretchColoring selected replacement n σ τ v)) =
      (∏ v, w (σ v)) * ∏ i, ∏ k, w (τ (i,k)) := by
  rw [← (g.stretchLabelVertexEquiv selected replacement n).prod_comp]
  simp only [stretchColoring_vertex,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    Fintype.prod_prod_type]

theorem sum_private_weighted_paths {A : Type} [Fintype A] [DecidableEq A] (n : ℕ)
    (M : Matrix C C R) (w : C → R) (x y : A → C) :
    (∑ τ : A × Fin n → C, ∏ i : A, PathPower.weightedWeight n M w (x i) (y i) (fun k => τ (i,k))) =
      ∏ i : A, (M * (Matrix.diagonal w * M)^n) (x i) (y i) := by
  calc
    _ = ∑ τ : A → Fin n → C, ∏ i : A, PathPower.weightedWeight n M w (x i) (y i) (τ i) := by
      apply Fintype.sum_equiv (Equiv.curry A (Fin n) C)
      intro τ
      rfl
    _ = ∏ i : A, ∑ τ : Fin n → C, PathPower.weightedWeight n M w (x i) (y i) τ :=
      (Fintype.prod_sum _).symm
    _ = _ := by simp only [PathPower.sum_weightedWeight]

/-- Replace the selected label by any matrix and keep the companion alphabet. -/
def substituteLabels {a b : ℕ} (M : Fin b → Matrix C C R)
    (selected : ℕ) (N : Matrix C C R) : Fin a → Matrix C C R :=
  fun l => if l.val=selected then N else if h : l.val<b then M ⟨l.val,h⟩ else 0

theorem substituteLabelsBinaryProduct {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected : ℕ) (N : Matrix C C R)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C) :
    (g.edges.map (binaryValue g.vertices a (substituteLabels M selected N) σ)).prod =
      (∏ i : Fin (g.selectedGraph selected).edges.length,
        N
          (σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).src i))
          (σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).dst i))) *
      ((g.companionEdges selected).map (binaryValue g.vertices b M σ)).prod := by
  rw [prod_map_get, ← (g.stretchEdgePartition selected).prod_comp]
  rw [Fintype.prod_sum_type, prod_map_get]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hv := hg.1 _ (List.get_mem g.edges (g.stretchEdgePartition selected (.inl i)))
    have hl : (g.edges.get (g.stretchEdgePartition selected (.inl i))).2.2=selected :=
      (g.selectedOccurrenceEquiv selected i).property
    have hsel : selected<a := by simpa only [hl] using hv.2.2
    simp only [binaryValue, hv.1, hv.2.1, hsel, and_self, ↓reduceDIte,
      substituteLabels, hl, ↓reduceIte, GraphCode.toMultiGraph, g.selectedGraph_get_partition selected i]
  · apply Finset.prod_congr rfl
    intro i _
    rw [companionEdges_get_partition]
    have hm := List.get_mem g.edges (g.stretchEdgePartition selected (.inr i))
    have hv := hg.1 _ hm
    have hl : (g.edges.get (g.stretchEdgePartition selected (.inr i))).2.2≠selected :=
      (g.companionOccurrenceEquiv selected i).property
    have hb := hkeep _ hm hl
    simp only [binaryValue, hv.1, hv.2.1, hv.2.2, hb, and_self, ↓reduceDIte,
      substituteLabels, hl, ↓reduceIte]


/-- Exact weighted path substitution, with all original unary and background
factors retained and every private vertex weighted once. Includes old loops. -/
theorem evaluate_stretchLabel_weighted {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected n : ℕ) (replacement : Fin b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R) :
    (g.stretchLabel selected replacement.val n).evaluate
      (g.stretchLabel_valid hg selected replacement.val n replacement.isLt hkeep) M U w =
    g.evaluate hg (substituteLabels M selected
      (M replacement * (Matrix.diagonal w * M replacement)^n)) U w := by
  simp only [evaluate]
  rw [sum_stretchColorings]
  apply Finset.sum_congr rfl
  intro σ _
  have hu (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C) :
      ((g.stretchLabel selected replacement.val n).unaries.map
        (unaryValue (g.stretchLabel selected replacement.val n).vertices u U
          (g.stretchColoring selected replacement.val n σ τ))).prod =
      (g.unaries.map (unaryValue g.vertices u U σ)).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    exact g.unaryValue_stretchColoring selected replacement.val n U σ τ e (hg.2 e he)
  simp_rw [stretch_vertex_weights,hu,
    stretchBinaryProduct g hg selected replacement.val n replacement.isLt hkeep M σ]
  rw [substituteLabelsBinaryProduct g hg selected _ hkeep M σ]
  let A := Fin (g.selectedGraph selected).edges.length
  let G := (g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)
  calc
    _ = (∏ v,w (σ v)) *
        (∑ τ : A × Fin n → C, ∏ i : A,
          PathPower.weightedWeight n (M replacement) w (σ (G.src i)) (σ (G.dst i)) (fun k => τ (i,k))) *
        ((g.companionEdges selected).map (binaryValue g.vertices b M σ)).prod *
        (g.unaries.map (unaryValue g.vertices u U σ)).prod := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      simp only [PathPower.weightedWeight,Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [sum_private_weighted_paths]
      ring

end PlanarHom.Complexity.MixedCode
