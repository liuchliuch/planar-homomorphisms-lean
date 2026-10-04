import PlanarHom.GraphComponentCode
import PlanarHom.FilteredOccurrenceEquiv
import PlanarHom.IncidenceEmbedding

/-! Every extracted component is an ordinary planar subgraph; vertex and edge
injections retain occurrence identity even for equal endpoint/label words. -/
noncomputable section
namespace PlanarHom.GraphComponentCode
open Complexity
variable {bt ut : ℕ}

def extractVertexEmbedding (g : MixedCode) (xs : List ℕ) (hn : xs.Nodup)
    (hb : ∀ v ∈ xs, v < g.vertices) : Fin xs.length ↪ Fin g.vertices where
  toFun i := ⟨xs.get i,hb _ (List.get_mem _ _)⟩
  inj' _ _ h := List.nodup_iff_injective_get.mp hn (congrArg Fin.val h)

def extractEdgeEmbedding (g : MixedCode) (xs : List ℕ) :
    Fin (extract g xs).edges.length ↪ Fin g.edges.length :=
  ((finCongr (extract_edges_length g xs)).toEmbedding.trans
    (FilteredOccurrence.equiv g.edges (edgeInside xs)).toEmbedding).trans (Function.Embedding.subtype _)

theorem extract_get_edge (g : MixedCode) (xs : List ℕ) (i : Fin (extract g xs).edges.length) :
    (extract g xs).edges.get i =
      (xs.idxOf (g.edges.get (extractEdgeEmbedding g xs i)).1,
        xs.idxOf (g.edges.get (extractEdgeEmbedding g xs i)).2.1,
        (g.edges.get (extractEdgeEmbedding g xs i)).2.2) := by
  have h := FilteredOccurrence.get_equiv g.edges (edgeInside xs)
    (Fin.cast (extract_edges_length g xs) i)
  change (g.edges.filter (edgeInside xs)).get (Fin.cast (extract_edges_length g xs) i) =
    g.edges.get (extractEdgeEmbedding g xs i) at h
  simp only [extract,List.get_eq_getElem,List.getElem_map]
  rw [show (g.edges.filter (edgeInside xs))[i.val] = g.edges.get (extractEdgeEmbedding g xs i) from h]
  simp only [List.get_eq_getElem]
  rfl

def extractIncidenceEmbedding (g : MixedCode) (hg : g.Valid bt ut) (xs : List ℕ)
    (hn : xs.Nodup) (hb : ∀ v ∈ xs, v < g.vertices) :
    MultiGraph.IncidenceEmbedding
      ((extract g xs).toMultiGraph (extract_valid g hg xs)) (g.toMultiGraph hg) where
  vertex := extractVertexEmbedding g xs hn hb
  edge := extractEdgeEmbedding g xs
  src_eq i := by
    apply Fin.ext
    change (g.edges.get (extractEdgeEmbedding g xs i)).1 = xs.get _
    have hi := extract_get_edge g xs i
    simp only [MixedCode.toMultiGraph]
    simp only [List.get_eq_getElem] at hi ⊢
    simp only [hi]
    symm
    exact List.getElem_idxOf _
  dst_eq i := by
    apply Fin.ext
    change (g.edges.get (extractEdgeEmbedding g xs i)).2.1 = xs.get _
    have hi := extract_get_edge g xs i
    simp only [MixedCode.toMultiGraph]
    simp only [List.get_eq_getElem] at hi ⊢
    simp only [hi]
    symm
    exact List.getElem_idxOf _

theorem extract_planarValid (g : MixedCode) (hg : g.PlanarValid bt ut) (xs : List ℕ)
    (hn : xs.Nodup) (hb : ∀ v ∈ xs, v < g.vertices) :
    (extract g xs).PlanarValid bt ut := by
  rw [MixedCode.planarValid_iff _ (extract_valid g hg.1 xs)]
  exact (extractIncidenceEmbedding g hg.1 xs hn hb).planar
    ((MixedCode.planarValid_iff g hg.1).mp hg)

end PlanarHom.GraphComponentCode
