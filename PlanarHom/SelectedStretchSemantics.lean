import PlanarHom.SelectedStretchPlanarity
import PlanarHom.PathPowerSemantics
import PlanarHom.MixedParallelSemantics

/-! Exact selected-path partition semantics. All new internal colors range
over the same full finite color space, and their background weight is one.
Prescribed-domain wrappers must supply this internal-domain condition. -/

noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.Complexity.MixedCode
variable {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]

theorem prod_map_get {α : Type*} (xs : List α) (f : α → R) :
    (xs.map f).prod = ∏ i : Fin xs.length, f (xs.get i) := by
  conv_lhs => rw [← List.ofFn_get xs]
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]

def stretchColoring (g : MixedCode) (selected replacement n : ℕ)
    (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C) :
    Fin (g.stretchLabel selected replacement n).vertices → C :=
  fun v => Sum.elim σ τ ((g.stretchLabelVertexEquiv selected replacement n).symm v)

omit [Fintype C] in
@[simp] theorem stretchColoring_vertex (g : MixedCode) (selected replacement n : ℕ)
    (σ : Fin g.vertices → C) (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C)
    (v : Fin g.vertices ⊕ (Fin (g.selectedGraph selected).edges.length × Fin n)) :
    g.stretchColoring selected replacement n σ τ (g.stretchLabelVertexEquiv selected replacement n v) =
      Sum.elim σ τ v := by simp [stretchColoring]

@[simp] theorem stretchColoring_old (g : MixedCode) (selected replacement n : ℕ)
    (σ : Fin g.vertices → C) (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C)
    (v : Fin g.vertices)
    (hv : v.val < (g.stretchLabel selected replacement n).vertices) :
    g.stretchColoring selected replacement n σ τ ⟨v.val,hv⟩ = σ v := by
  change g.stretchColoring selected replacement n σ τ
    (g.stretchLabelVertexEquiv selected replacement n (.inl v)) = _
  exact g.stretchColoring_vertex selected replacement n σ τ (.inl v)

theorem unaryValue_stretchColoring {u : ℕ} (g : MixedCode) (selected replacement n : ℕ)
    (U : Fin u → C → R) (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C)
    (e : ℕ × ℕ) (he : e.1<g.vertices ∧ e.2<u) :
    unaryValue (g.stretchLabel selected replacement n).vertices u U
      (g.stretchColoring selected replacement n σ τ) e = unaryValue g.vertices u U σ e := by
  have hV : e.1<(g.stretchLabel selected replacement n).vertices := by
    rw [stretchLabel_vertices]; omega
  simp only [unaryValue, he.1, he.2, hV, and_self, ↓reduceDIte]
  exact congrArg (U ⟨e.2,he.2⟩) (g.stretchColoring_old selected replacement n σ τ ⟨e.1,he.1⟩ hV)

theorem binaryValue_stretchColoring {b : ℕ} (g : MixedCode) (selected replacement n : ℕ)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C)
    (e : ℕ × (ℕ × ℕ)) (he : e.1<g.vertices ∧ e.2.1<g.vertices ∧ e.2.2<b) :
    binaryValue (g.stretchLabel selected replacement n).vertices b M
      (g.stretchColoring selected replacement n σ τ) e = binaryValue g.vertices b M σ e := by
  have hV : g.vertices≤(g.stretchLabel selected replacement n).vertices := by
    rw [stretchLabel_vertices]; omega
  have h₁ := he.1.trans_le hV
  have h₂ := he.2.1.trans_le hV
  simp only [binaryValue, he.1, he.2.1, he.2.2, h₁, h₂, and_self, ↓reduceDIte]
  rw [g.stretchColoring_old selected replacement n σ τ ⟨e.1,he.1⟩ h₁,
    g.stretchColoring_old selected replacement n σ τ ⟨e.2.1,he.2.1⟩ h₂]

theorem path_binaryValue {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected replacement n : ℕ) (hr : replacement<b)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C)
    (p : Fin (g.selectedGraph selected).edges.length × Fin (n+1)) :
    binaryValue (g.stretchLabel selected replacement n).vertices b M
      (g.stretchColoring selected replacement n σ τ)
      (((g.selectedGraph selected).stretchEndpoints n p).1,
        ((g.selectedGraph selected).stretchEndpoints n p).2,replacement) =
    M ⟨replacement,hr⟩
      (PathPower.sourceColor n (σ (((g.selectedGraph selected).toMultiGraph
        (g.selectedGraph_valid hg selected)).src p.1)) (fun k => τ (p.1,k)) p.2)
      (PathPower.targetColor n (σ (((g.selectedGraph selected).toMultiGraph
        (g.selectedGraph_valid hg selected)).dst p.1)) (fun k => τ (p.1,k)) p.2) := by
  have hv := (g.selectedGraph selected).stretchEndpoints_valid (g.selectedGraph_valid hg selected) n p
  change ((g.selectedGraph selected).stretchEndpoints n p).1 <
      (g.stretchLabel selected replacement n).vertices ∧
    ((g.selectedGraph selected).stretchEndpoints n p).2 <
      (g.stretchLabel selected replacement n).vertices at hv
  simp only [binaryValue, hv.1, hv.2, hr, and_self, ↓reduceDIte]
  have hs := ((g.selectedGraph selected).stretchIncidenceEquiv (g.selectedGraph_valid hg selected) n).src_eq p
  have ht := ((g.selectedGraph selected).stretchIncidenceEquiv (g.selectedGraph_valid hg selected) n).dst_eq p
  simp only [GraphCode.stretchIncidenceEquiv, GraphCode.toMultiGraph, GraphCode.stretch_get,
    MultiGraph.stretch] at hs ht
  change M ⟨replacement,hr⟩
    (g.stretchColoring selected replacement n σ τ _)
    (g.stretchColoring selected replacement n σ τ _) = _
  have hc (v : Fin g.vertices ⊕ (Fin (g.selectedGraph selected).edges.length × Fin n)) :
      g.stretchColoring selected replacement n σ τ ((g.selectedGraph selected).stretchVertexEquiv n v) =
        Sum.elim σ τ v := g.stretchColoring_vertex selected replacement n σ τ v
  rw [hs, ht, hc, hc]
  congr 1
  · by_cases hk : p.2.val=0 <;>
      simp [MultiGraph.stretchSrc, PathPower.sourceColor, hk, GraphCode.toMultiGraph]
  · by_cases hk : p.2.val=n <;>
      simp [MultiGraph.stretchDst, PathPower.targetColor, hk, GraphCode.toMultiGraph]

theorem sum_stretchColorings (g : MixedCode) (selected replacement n : ℕ)
    (f : (Fin (g.stretchLabel selected replacement n).vertices → C) → R) :
    (∑ ω, f ω) = ∑ σ : Fin g.vertices → C,
      ∑ τ : Fin (g.selectedGraph selected).edges.length × Fin n → C,
        f (g.stretchColoring selected replacement n σ τ) := by
  let e : ((Fin g.vertices → C) × (Fin (g.selectedGraph selected).edges.length × Fin n → C)) ≃
      (Fin (g.stretchLabel selected replacement n).vertices → C) :=
    (Equiv.sumArrowEquivProdArrow (Fin g.vertices)
      (Fin (g.selectedGraph selected).edges.length × Fin n) C).symm.trans
        ((g.stretchLabelVertexEquiv selected replacement n).arrowCongr (Equiv.refl C))
  calc
    _ = ∑ p : (Fin g.vertices → C) × (Fin (g.selectedGraph selected).edges.length × Fin n → C),
        f (g.stretchColoring selected replacement n p.1 p.2) := (e.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem stretchBinaryProduct {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected replacement n : ℕ) (hr : replacement<b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C)
    (τ : Fin (g.selectedGraph selected).edges.length × Fin n → C) :
    ((g.stretchLabel selected replacement n).edges.map
      (binaryValue (g.stretchLabel selected replacement n).vertices b M
        (g.stretchColoring selected replacement n σ τ))).prod =
      (∏ i : Fin (g.selectedGraph selected).edges.length,
        PathPower.weight n (M ⟨replacement,hr⟩)
          (σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).src i))
          (σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).dst i))
          (fun k => τ (i,k))) *
      ((g.companionEdges selected).map (binaryValue g.vertices b M σ)).prod := by
  rw [prod_map_get]
  rw [← (g.stretchLabelEdgeEquiv selected replacement n).prod_comp]
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, prod_map_get]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro k _
    rw [stretchLabel_get_left]
    exact g.path_binaryValue hg selected replacement n hr M σ τ (i,k)
  · apply Finset.prod_congr rfl
    intro i _
    rw [stretchLabel_get_right]
    have hm := (List.mem_filter.mp (List.get_mem (g.companionEdges selected) i))
    have hv := hg.1 _ hm.1
    exact g.binaryValue_stretchColoring selected replacement n M σ τ _
      ⟨hv.1,hv.2.1,hkeep _ hm.1 (by simpa using hm.2)⟩

/-- All selected occurrences have independent private internal assignments. -/
theorem sum_private_path_weights {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ)
    (M : Matrix C C R) (x y : A → C) :
    (∑ τ : A × Fin n → C, ∏ i : A, PathPower.weight n M (x i) (y i) (fun k => τ (i,k))) =
      ∏ i : A, (M^(n+1)) (x i) (y i) := by
  calc
    _ = ∑ τ : A → Fin n → C, ∏ i : A, PathPower.weight n M (x i) (y i) (τ i) := by
      apply Fintype.sum_equiv (Equiv.curry A (Fin n) C)
      intro τ
      rfl
    _ = ∏ i : A, ∑ τ : Fin n → C, PathPower.weight n M (x i) (y i) τ :=
      (Fintype.prod_sum _).symm
    _ = _ := by simp only [PathPower.sum_weight]

/-- The target alphabet may contain an extra auxiliary label. Every retained
source label keeps its original numeric index; unused out-of-range labels have
a total zero default. On promised instances `hkeep` excludes that default. -/
def pathPowerLabels {a b : ℕ} (M : Fin b → Matrix C C R)
    (selected : ℕ) (replacement : Fin b) (n : ℕ) : Fin a → Matrix C C R :=
  fun l => if l.val=selected then M replacement^(n+1)
    else if h : l.val<b then M ⟨l.val,h⟩ else 0

theorem powerLabelsBinaryProduct {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected n : ℕ) (replacement : Fin b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C) :
    (g.edges.map (binaryValue g.vertices a (pathPowerLabels M selected replacement n) σ)).prod =
      (∏ i : Fin (g.selectedGraph selected).edges.length,
        (M replacement^(n+1))
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
      pathPowerLabels, hl, ↓reduceIte, GraphCode.toMultiGraph, g.selectedGraph_get_partition selected i]
  · apply Finset.prod_congr rfl
    intro i _
    rw [companionEdges_get_partition]
    have hm := List.get_mem g.edges (g.stretchEdgePartition selected (.inr i))
    have hv := hg.1 _ hm
    have hl : (g.edges.get (g.stretchEdgePartition selected (.inr i))).2.2≠selected :=
      (g.companionOccurrenceEquiv selected i).property
    have hb := hkeep _ hm hl
    simp only [binaryValue, hv.1, hv.2.1, hv.2.2, hb, and_self, ↓reduceDIte,
      pathPowerLabels, hl, ↓reduceIte]

/-- Exact mixed partition identity for unequal input/output alphabet sizes.
The unit background and unrestricted private color sums are explicit. No
condition excludes input loops or repeated binary/unary occurrences. -/
theorem evaluate_stretchLabel {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected n : ℕ) (replacement : Fin b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) :
    (g.stretchLabel selected replacement.val n).evaluate
      (g.stretchLabel_valid hg selected replacement.val n replacement.isLt hkeep) M U (fun _ => 1) =
    g.evaluate hg (pathPowerLabels M selected replacement n) U (fun _ => 1) := by
  simp only [evaluate, Finset.prod_const_one, one_mul]
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
  simp_rw [hu, stretchBinaryProduct g hg selected replacement.val n replacement.isLt hkeep M σ]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [powerLabelsBinaryProduct g hg selected n replacement hkeep M σ]
  exact congrArg (fun z : R => z *
    ((g.companionEdges selected).map (binaryValue g.vertices b M σ)).prod *
    (g.unaries.map (unaryValue g.vertices u U σ)).prod)
    (sum_private_path_weights n (M replacement)
      (fun i => σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).src i))
      (fun i => σ (((g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected)).dst i)))

end PlanarHom.Complexity.MixedCode
