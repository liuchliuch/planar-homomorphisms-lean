import PlanarHom.MixedLabelExpansionMachines
import PlanarHom.PlanarRibbonExistence

/-!
# Exact occurrence indexing and ordinary planarity for finite label words

Each binary occurrence is expanded into its fixed target-label word. The
incidence equivalence below uses the actual flatMap output positions: repeated
labels and equal endpoints remain distinct occurrences, empty words contribute
no edge, and loops retain their endpoints. Ordinary source planarity supplies
the finite ribbons used by occurrence-dependent replication.
-/

namespace PlanarHom.ReplicationIndex

theorem map_copies_wordMap {α β γ : Type*} (xs : List α) (word : α → List β)
    (value : α → β → γ) :
    (copies (fun i => (word (xs.get i)).length)).map
      (fun p => value (xs.get p.1) ((word (xs.get p.1)).get p.2)) =
        xs.flatMap (fun x => (word x).map (value x)) := by
  simp only [copies, List.sigma, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [← List.ofFn_eq_map, List.ofFn_comp', List.ofFn_get]
  have hx : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  calc
    _ = ((List.finRange xs.length).map xs.get).flatMap
        (fun x => (word x).map (value x)) := by rw [List.flatMap_map]
    _ = _ := by rw [hx]

theorem copies_wordMap_length {α β γ : Type*} (xs : List α) (word : α → List β)
    (value : α → β → γ) :
    (copies (fun i => (word (xs.get i)).length)).length =
      (xs.flatMap (fun x => (word x).map (value x))).length := by
  simpa using congrArg List.length (map_copies_wordMap xs word value)

noncomputable def wordMapEquiv {α β γ : Type*} (xs : List α) (word : α → List β)
    (value : α → β → γ) :
    Fin (xs.flatMap (fun x => (word x).map (value x))).length ≃
      Σ i : Fin xs.length, Fin (word (xs.get i)).length :=
  (finCongr (copies_wordMap_length xs word value).symm).trans
    ((copies_nodup _).getEquivOfForallMemList _ (mem_copies _))

theorem get_wordMapEquiv {α β γ : Type*} (xs : List α) (word : α → List β)
    (value : α → β → γ)
    (j : Fin (xs.flatMap (fun x => (word x).map (value x))).length) :
    (xs.flatMap (fun x => (word x).map (value x))).get j =
      value (xs.get (wordMapEquiv xs word value j).1)
        ((word (xs.get (wordMapEquiv xs word value j).1)).get
          (wordMapEquiv xs word value j).2) := by
  have hi : j.val < (copies (fun i => (word (xs.get i)).length)).length := by
    rw [copies_wordMap_length xs word value]
    exact j.isLt
  have hget := congrArg (fun l : List γ => l[j.val]?) (map_copies_wordMap xs word value)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem j.isLt, Option.map_some] at hget
  exact (Option.some.inj hget).symm

end PlanarHom.ReplicationIndex


noncomputable section
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLabelWordLookupMachines

/-- An output position is exactly a source occurrence and a word position. -/
def expandBinaryWordsEdgeEquiv (g : MixedCode) (table : List (ℕ × List ℕ)) :
    (Σ e : Fin g.edges.length, Fin (lookup table (g.edges.get e).2.2).length) ≃
      Fin (g.expandBinaryWords table).edges.length :=
  (ReplicationIndex.wordMapEquiv g.edges (fun e => lookup table e.2.2)
    (fun e label => (e.1,e.2.1,label))).symm

/-- The exact output triple has both original endpoints and the indexed new label. -/
theorem expandBinaryWords_get (g : MixedCode) (table : List (ℕ × List ℕ))
    (p : Σ e : Fin g.edges.length, Fin (lookup table (g.edges.get e).2.2).length) :
    (g.expandBinaryWords table).edges.get (g.expandBinaryWordsEdgeEquiv table p) =
      ((g.edges.get p.1).1,(g.edges.get p.1).2.1,
        (lookup table (g.edges.get p.1).2.2).get p.2) := by
  change (g.edges.flatMap (fun e => (lookup table e.2.2).map
    (fun label => (e.1,e.2.1,label)))).get
      ((ReplicationIndex.wordMapEquiv g.edges (fun e => lookup table e.2.2)
        (fun e label => (e.1,e.2.1,label))).symm p) = _
  rw [ReplicationIndex.get_wordMapEquiv, Equiv.apply_symm_apply]

/-- Exact incidence identification with finite geometric edge replication. -/
def expandBinaryWordsIncidenceEquiv {a b u : ℕ} (g : MixedCode)
    (hg : g.Valid a u) (table : List (ℕ × List ℕ))
    (hlabels : ∀i,i<a→∀j∈lookup table i,j<b) :
    MultiGraph.IncidenceEquiv
      ((g.toMultiGraph hg).replicateOccurrences
        (fun e => (lookup table (g.edges.get e).2.2).length))
      ((g.expandBinaryWords table).toMultiGraph (expandBinaryWords_valid table hg hlabels)) where
  vertex := Equiv.refl _
  edge := g.expandBinaryWordsEdgeEquiv table
  src_eq p := by
    apply Fin.ext
    change ((g.expandBinaryWords table).edges.get (g.expandBinaryWordsEdgeEquiv table p)).1 = _
    rw [expandBinaryWords_get]
    rfl
  dst_eq p := by
    apply Fin.ext
    change ((g.expandBinaryWords table).edges.get (g.expandBinaryWordsEdgeEquiv table p)).2.1 = _
    rw [expandBinaryWords_get]
    rfl

/-- Finite parallel label-word expansion preserves the ordinary planar promise,
including empty words and source loops, without any supplied drawing certificate. -/
theorem expandBinaryWords_planar (table : List (ℕ × List ℕ)) {g : MixedCode} {a b u : ℕ}
    (hg : g.PlanarValid a u) (hlabels : ∀i,i<a→∀j∈lookup table i,j<b) :
    (g.expandBinaryWords table).PlanarValid b u := by
  have hv := expandBinaryWords_valid table hg.1 hlabels
  apply ((g.expandBinaryWords table).planarValid_iff hv).mpr
  exact (g.expandBinaryWordsIncidenceEquiv hg.1 table hlabels).planar_iff.mp
    (((g.planarValid_iff hg.1).mp hg).replicateOccurrences _)

end PlanarHom.Complexity.MixedCode
