import PlanarHom.ReplicationIndexEquiv
import PlanarHom.PlanarTransport
import PlanarHom.PlanarRibbons
import PlanarHom.PlanarGraphCode
import PlanarHom.MixedPlanarCode
import PlanarHom.MixedParallelCode

/-!
# Exact geometric/code bridges for occurrence-dependent thickening

These theorems identify the actual compiled occurrence lists with the geometric
multigraph replacement, including selected binary labels and zero copy counts.
Planarity is constructed from explicit edge ribbons. They do not assert that
arbitrary ordinary planar drawings have those ribbon certificates; that remains
the separate regular-neighborhood obligation.
-/

noncomputable section
namespace PlanarHom
namespace MultiGraph

/-- Each original occurrence has its own finite number of distinct copies. -/
def replicateOccurrences {V E : Type*} (G : MultiGraph V E) (count : E → ℕ) :
    MultiGraph V (Σ e : E, Fin (count e)) where
  src p := G.src p.1
  dst p := G.dst p.1

namespace RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Explicit curves for edge-dependent copy counts in disjoint ribbons. -/
def replicateDrawing (d : RibbonDrawing G) (count : E → ℕ) :
    PlaneDrawing (G.replicateOccurrences count) where
  point := d.point
  point_injective := d.point_injective
  curve p := (d.band p.1).comp (slice (level p.2))
  curve_zero p := d.band_zero p.1 _
  curve_one p := d.band_one p.1 _
  interior_injective := by
    rintro ⟨e,k⟩ ⟨f,l⟩ s t hs ht h
    obtain ⟨hef,hst⟩ := d.band_injective e f (s,level k) (t,level l) hs ht h
    subst f
    have hkl := level_injective (congrArg Prod.snd hst)
    exact ⟨by cases hkl; rfl, congrArg Prod.fst hst⟩
  interior_avoids p t ht v := d.band_avoids p.1 (t,level p.2) ht v

theorem replicate_planar (d : RibbonDrawing G) (count : E → ℕ) :
    (G.replicateOccurrences count).Planar := ⟨d.replicateDrawing count⟩

end RibbonDrawing
end MultiGraph

namespace Complexity
namespace GraphCode

/-- Raw occurrence-wise replication; counts depend only on the actual endpoint
pair here. Mixed selected-label replication is handled below before forgetting labels. -/
def replicateOccurrences (g : GraphCode) (count : (ℕ × ℕ) → ℕ) : GraphCode :=
  ⟨g.vertices,g.edges.flatMap (fun e => List.replicate (count e) e)⟩

theorem replicateOccurrences_valid (g : GraphCode) (hg : g.Valid) (count : (ℕ × ℕ) → ℕ) :
    (g.replicateOccurrences count).Valid := by
  intro e he
  obtain ⟨a,ha,hrep⟩ := List.mem_flatMap.mp he
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hrep
  exact hg _ ha

/-- Bijection from geometric occurrence/copy pairs to the real output positions. -/
def replicationIncidenceEquiv (g : GraphCode) (hg : g.Valid) (count : (ℕ × ℕ) → ℕ) :
    MultiGraph.IncidenceEquiv
      ((g.toMultiGraph hg).replicateOccurrences (fun e => count (g.edges.get e)))
      ((g.replicateOccurrences count).toMultiGraph (g.replicateOccurrences_valid hg count)) where
  vertex := Equiv.refl _
  edge := (ReplicationIndex.replicateEquiv g.edges count).symm
  src_eq p := by
    apply Fin.ext
    change ((g.edges.flatMap (fun e => List.replicate (count e) e)).get
      ((ReplicationIndex.replicateEquiv g.edges count).symm p)).1 = _
    rw [ReplicationIndex.get_replicateEquiv, Equiv.apply_symm_apply]
    rfl
  dst_eq p := by
    apply Fin.ext
    change ((g.edges.flatMap (fun e => List.replicate (count e) e)).get
      ((ReplicationIndex.replicateEquiv g.edges count).symm p)).2 = _
    rw [ReplicationIndex.get_replicateEquiv, Equiv.apply_symm_apply]
    rfl

/-- Actual output-code planarity from an explicit source ribbon drawing. -/
theorem replicate_planar_of_ribbon (g : GraphCode) (hg : g.Valid)
    (d : MultiGraph.RibbonDrawing (g.toMultiGraph hg)) (count : (ℕ × ℕ) → ℕ) :
    (g.replicateOccurrences count).PlanarValid := by
  refine ⟨g.replicateOccurrences_valid hg count, ?_⟩
  exact (g.replicationIncidenceEquiv hg count).planar_iff.mp (d.replicate_planar _)

/-- Bridge to the existing uniform-thickening compiler's exact GraphCode output.
The ribbon hypothesis is visible; ordinary input planarity alone is not claimed. -/
theorem parallel_planar_of_ribbon (g : GraphCode) (hg : g.Valid)
    (d : MultiGraph.RibbonDrawing (g.toMultiGraph hg)) (s : ℕ) :
    (g.parallel s).PlanarValid := g.replicate_planar_of_ribbon hg d (fun _ => s)

end GraphCode

namespace MixedCode

/-- Copy count for an actual binary-labelled occurrence. -/
def selectedCount (selected s : ℕ) (e : ℕ × (ℕ × ℕ)) : ℕ :=
  if e.2.2 = selected then s else 1

theorem parallelLabel_edges_eq (g : MixedCode) (selected s : ℕ) :
    (g.parallelLabel selected s).edges =
      g.edges.flatMap (fun e => List.replicate (selectedCount selected s e) e) := by
  unfold parallelLabel repeatSelected
  apply congrArg (fun f => g.edges.flatMap f)
  funext e
  by_cases he : e.2.2 = selected <;> simp [selectedCount,he]

private theorem get_cast_of_eq {α : Type*} {xs ys : List α} (h : xs = ys) (i : Fin xs.length) :
    ys.get (finCongr (congrArg List.length h) i) = xs.get i := by
  cases h
  rfl

/-- The selected-label compiler retains exact occurrence identity, including
unmatched singleton occurrences and selected occurrences with zero copies. -/
def parallelLabelEdgeEquiv (g : MixedCode) (selected s : ℕ) :
    (Σ e : Fin g.edges.length, Fin (selectedCount selected s (g.edges.get e))) ≃
      Fin (g.parallelLabel selected s).edges.length :=
  (ReplicationIndex.replicateEquiv g.edges (selectedCount selected s)).symm.trans
    (finCongr (congrArg List.length (g.parallelLabel_edges_eq selected s)).symm)

theorem parallelLabel_get (g : MixedCode) (selected s : ℕ)
    (p : Σ e : Fin g.edges.length, Fin (selectedCount selected s (g.edges.get e))) :
    (g.parallelLabel selected s).edges.get (g.parallelLabelEdgeEquiv selected s p) =
      g.edges.get p.1 := by
  unfold parallelLabelEdgeEquiv
  rw [Equiv.trans_apply, get_cast_of_eq (g.parallelLabel_edges_eq selected s).symm]
  rw [ReplicationIndex.get_replicateEquiv, Equiv.apply_symm_apply]

/-- Full selected-label occurrence identification, prior to forgetting labels. -/
def parallelLabelIncidenceEquiv {binaryTypes unaryTypes : ℕ}
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) (selected s : ℕ) :
    MultiGraph.IncidenceEquiv
      ((g.toMultiGraph hg).replicateOccurrences
        (fun e => selectedCount selected s (g.edges.get e)))
      ((g.parallelLabel selected s).toMultiGraph
        (g.parallelLabel_valid selected s binaryTypes unaryTypes hg)) where
  vertex := Equiv.refl _
  edge := g.parallelLabelEdgeEquiv selected s
  src_eq p := by
    apply Fin.ext
    change ((g.parallelLabel selected s).edges.get (g.parallelLabelEdgeEquiv selected s p)).1 = _
    rw [parallelLabel_get]
    rfl
  dst_eq p := by
    apply Fin.ext
    change ((g.parallelLabel selected s).edges.get (g.parallelLabelEdgeEquiv selected s p)).2.1 = _
    rw [parallelLabel_get]
    rfl

/-- Planarity of the compiler's actual mixed query, from explicit source ribbons.
All existing binary labels, unary occurrences and vertices remain governed by the
unchanged `parallelLabel` transformation and its endpoint/label validity theorem. -/
theorem parallelLabel_planar_of_ribbon {binaryTypes unaryTypes : ℕ}
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (d : MultiGraph.RibbonDrawing (g.toMultiGraph hg)) (selected s : ℕ) :
    (g.parallelLabel selected s).PlanarValid binaryTypes unaryTypes := by
  have hv := g.parallelLabel_valid selected s binaryTypes unaryTypes hg
  apply ((g.parallelLabel selected s).planarValid_iff hv).mpr
  exact (g.parallelLabelIncidenceEquiv hg selected s).planar_iff.mp (d.replicate_planar _)

end MixedCode
end Complexity
end PlanarHom
