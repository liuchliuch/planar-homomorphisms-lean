import PlanarHom.SelectedStretchCode
import PlanarHom.FilteredOccurrenceEquiv
import PlanarHom.PlanarSelectedStretch

/-! Explicit incidence equivalences identify the emitted mixed list with
selected topological edge stretching. No drawing is part of the raw input. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode

def selectedOccurrenceEquiv (g : MixedCode) (selected : ℕ) :
    Fin (g.selectedGraph selected).edges.length ≃
      {i : Fin g.edges.length // (g.edges.get i).2.2=selected} :=
  ((finCongr (g.selectedGraph_edges_length selected)).trans
    (FilteredOccurrence.equiv g.edges (fun e => decide (e.2.2=selected)))).trans
      (Equiv.subtypeEquivRight (fun _ => by simp))

def companionOccurrenceEquiv (g : MixedCode) (selected : ℕ) :
    Fin (g.companionEdges selected).length ≃
      {i : Fin g.edges.length // ¬(g.edges.get i).2.2=selected} :=
  (FilteredOccurrence.equiv g.edges (fun e => decide (e.2.2≠selected))).trans
    (Equiv.subtypeEquivRight (fun _ => by simp))

/-- Stable original occurrence identities partitioned by the selected label. -/
def stretchEdgePartition (g : MixedCode) (selected : ℕ) :
    Fin (g.selectedGraph selected).edges.length ⊕ Fin (g.companionEdges selected).length ≃
      Fin g.edges.length :=
  (Equiv.sumCongr (g.selectedOccurrenceEquiv selected) (g.companionOccurrenceEquiv selected)).trans
    (Equiv.sumCompl (fun i : Fin g.edges.length => (g.edges.get i).2.2=selected))

theorem selectedGraph_get_partition (g : MixedCode) (selected : ℕ)
    (i : Fin (g.selectedGraph selected).edges.length) :
    (g.selectedGraph selected).edges.get i =
      ((g.edges.get (g.stretchEdgePartition selected (.inl i))).1,
        (g.edges.get (g.stretchEdgePartition selected (.inl i))).2.1) := by
  have he := FilteredOccurrence.get_equiv g.edges (fun e => decide (e.2.2=selected))
    (Fin.cast (g.selectedGraph_edges_length selected) i)
  change (g.selectedEdges selected).get (Fin.cast (g.selectedGraph_edges_length selected) i) =
    g.edges.get (g.stretchEdgePartition selected (.inl i)) at he
  simpa [selectedGraph, List.get_eq_getElem] using congrArg (fun e : ℕ × (ℕ × ℕ) => (e.1,e.2.1)) he

theorem companionEdges_get_partition (g : MixedCode) (selected : ℕ)
    (i : Fin (g.companionEdges selected).length) :
    (g.companionEdges selected).get i = g.edges.get (g.stretchEdgePartition selected (.inr i)) :=
  FilteredOccurrence.get_equiv g.edges (fun e => decide (e.2.2≠selected)) i

theorem partitionLeft_eq_selectedGraph {a u : ℕ} (g : MixedCode) (hg : g.Valid a u) (selected : ℕ) :
    (g.toMultiGraph hg).partitionLeft (g.stretchEdgePartition selected) =
      (g.selectedGraph selected).toMultiGraph (g.selectedGraph_valid hg selected) := by
  unfold MultiGraph.partitionLeft toMultiGraph GraphCode.toMultiGraph
  congr 1 <;> funext i <;> apply Fin.ext
  · exact (congrArg Prod.fst (g.selectedGraph_get_partition selected i)).symm
  · exact (congrArg Prod.snd (g.selectedGraph_get_partition selected i)).symm

def stretchLabelVertexEquiv (g : MixedCode) (selected replacement n : ℕ) :
    Fin g.vertices ⊕ (Fin (g.selectedGraph selected).edges.length × Fin n) ≃
      Fin (g.stretchLabel selected replacement n).vertices :=
  (g.selectedGraph selected).stretchVertexEquiv n

def stretchLabelEdgeEquiv (g : MixedCode) (selected replacement n : ℕ) :
    (Fin (g.selectedGraph selected).edges.length × Fin (n+1)) ⊕
        Fin (g.companionEdges selected).length ≃ Fin (g.stretchLabel selected replacement n).edges.length :=
  ((Equiv.sumCongr ((g.selectedGraph selected).stretchEdgeEquiv n) (Equiv.refl _)).trans
    finSumFinEquiv).trans (finCongr (by simp [stretchLabel]))

theorem stretchLabel_get_left (g : MixedCode) (selected replacement n : ℕ)
    (p : Fin (g.selectedGraph selected).edges.length × Fin (n+1)) :
    (g.stretchLabel selected replacement n).edges.get
      (g.stretchLabelEdgeEquiv selected replacement n (.inl p)) =
        (((g.selectedGraph selected).stretchEndpoints n p).1,
          ((g.selectedGraph selected).stretchEndpoints n p).2,replacement) := by
  simp only [stretchLabelEdgeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_apply_left, stretchLabel, List.get_eq_getElem]
  rw [List.getElem_append_left (by simpa using ((g.selectedGraph selected).stretchEdgeEquiv n p).isLt)]
  simp only [List.getElem_map]
  exact congrArg (fun e : ℕ × ℕ => (e.1,e.2,replacement))
    ((g.selectedGraph selected).stretch_get n p)

theorem stretchLabel_get_right (g : MixedCode) (selected replacement n : ℕ)
    (i : Fin (g.companionEdges selected).length) :
    (g.stretchLabel selected replacement n).edges.get
      (g.stretchLabelEdgeEquiv selected replacement n (.inr i)) =
        (g.companionEdges selected).get i := by
  simp [stretchLabelEdgeEquiv, stretchLabel, List.get_eq_getElem]

/-- The exact finite bijections preserve both ordered endpoints of every
emitted segment and every unchanged companion, including loops. -/
def stretchLabelIncidenceEquiv {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected replacement n : ℕ) (hr : replacement<b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b) :
    MultiGraph.IncidenceEquiv
      ((g.toMultiGraph hg).selectedStretch (g.stretchEdgePartition selected) n)
      ((g.stretchLabel selected replacement n).toMultiGraph
        (g.stretchLabel_valid hg selected replacement n hr hkeep)) where
  vertex := g.stretchLabelVertexEquiv selected replacement n
  edge := g.stretchLabelEdgeEquiv selected replacement n
  src_eq p := by
    cases p with
    | inl p =>
      apply Fin.ext
      change ((g.stretchLabel selected replacement n).edges.get
        (g.stretchLabelEdgeEquiv selected replacement n (.inl p))).1 = _
      rw [stretchLabel_get_left]
      change _ = ((g.stretchLabelVertexEquiv selected replacement n)
        (((g.toMultiGraph hg).partitionLeft (g.stretchEdgePartition selected)).stretchSrc n p)).val
      rw [partitionLeft_eq_selectedGraph]
      simpa only [GraphCode.stretchIncidenceEquiv, GraphCode.toMultiGraph,
        GraphCode.stretch_get, stretchLabelVertexEquiv, MultiGraph.stretch] using
          congrArg Fin.val (((g.selectedGraph selected).stretchIncidenceEquiv
            (g.selectedGraph_valid hg selected) n).src_eq p)
    | inr i =>
      apply Fin.ext
      change ((g.stretchLabel selected replacement n).edges.get
        (g.stretchLabelEdgeEquiv selected replacement n (.inr i))).1 = _
      rw [stretchLabel_get_right, companionEdges_get_partition]
      rfl
  dst_eq p := by
    cases p with
    | inl p =>
      apply Fin.ext
      change ((g.stretchLabel selected replacement n).edges.get
        (g.stretchLabelEdgeEquiv selected replacement n (.inl p))).2.1 = _
      rw [stretchLabel_get_left]
      change _ = ((g.stretchLabelVertexEquiv selected replacement n)
        (((g.toMultiGraph hg).partitionLeft (g.stretchEdgePartition selected)).stretchDst n p)).val
      rw [partitionLeft_eq_selectedGraph]
      simpa only [GraphCode.stretchIncidenceEquiv, GraphCode.toMultiGraph,
        GraphCode.stretch_get, stretchLabelVertexEquiv, MultiGraph.stretch] using
          congrArg Fin.val (((g.selectedGraph selected).stretchIncidenceEquiv
            (g.selectedGraph_valid hg selected) n).dst_eq p)
    | inr i =>
      apply Fin.ext
      change ((g.stretchLabel selected replacement n).edges.get
        (g.stretchLabelEdgeEquiv selected replacement n (.inr i))).2.1 = _
      rw [stretchLabel_get_right, companionEdges_get_partition]
      rfl

theorem stretchLabel_planar {a b u : ℕ} (g : MixedCode) (hg : g.PlanarValid a u)
    (selected replacement n : ℕ) (hr : replacement<b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b) :
    (g.stretchLabel selected replacement n).PlanarValid b u := by
  apply ((g.stretchLabel selected replacement n).planarValid_iff
    (g.stretchLabel_valid hg.1 selected replacement n hr hkeep)).mpr
  exact (g.stretchLabelIncidenceEquiv hg.1 selected replacement n hr hkeep).planar_iff.mp
    (((g.planarValid_iff hg.1).mp hg).selectedStretch (g.stretchEdgePartition selected) n)

end PlanarHom.Complexity.MixedCode
