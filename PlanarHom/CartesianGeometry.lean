import PlanarHom.DistanceEmbedding
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Local Euclidean geometry for Cartesian product characterization

A complete proof of Lemma 4.6, using actual simple graphs. The proof constructs
local square translations, base-clique simplexes, exact neighbor frames, and
finite product coordinates; it then packages the coordinate bijection as a
`SimpleGraph.Iso`. The PSD-kernel hypothesis is discharged by the independently
proved squared-distance representation in `DistanceEmbedding`.
-/

noncomputable section

namespace PlanarHom.CartesianGeometry

open scoped InnerProductSpace BigOperators

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Each connected component of every induced neighborhood is a clique,
expressed as transitivity of adjacency-or-equality on that neighborhood. -/
def NeighborhoodCliques (G : SimpleGraph V) : Prop :=
  ∀ (o u v w : V), G.Adj o u → G.Adj o v → G.Adj o w →
    G.Adj u v → G.Adj v w → u = w ∨ G.Adj u w

/-- Every distance-two pair has exactly two nonadjacent common neighbors. -/
def TwoCommonNeighbors (G : SimpleGraph V) : Prop :=
  ∀ u v, G.dist u v = 2 → ∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧
    (∀ w, G.Adj u w ∧ G.Adj v w ↔ w = a ∨ w = b)

/-- A realization of graph distance by squared Euclidean distance. -/
def IsSquaredDistanceEmbedding (G : SimpleGraph V) (f : V → E) : Prop :=
  ∀ u v, ‖f u - f v‖ ^ 2 = (G.dist u v : ℝ)

variable {G : SimpleGraph V} {f : V → E}

omit [InnerProductSpace ℝ E] in
theorem IsSquaredDistanceEmbedding.injective (hf : IsSquaredDistanceEmbedding G f)
    (hG : G.Connected) : Function.Injective f := by
  intro u v huv
  apply hG.dist_eq_zero_iff.mp
  have h := hf u v
  rw [huv, sub_self, norm_zero, zero_pow (by decide)] at h
  exact_mod_cast h.symm

/-- Two distinct nonadjacent vertices with a common neighbor have distance two. -/
theorem dist_eq_two_of_common_neighbor {u v o : V} (huv : u ≠ v)
    (hn : ¬G.Adj u v) (hou : G.Adj o u) (hov : G.Adj o v) : G.dist u v = 2 := by
  let p : G.Walk u v := hou.symm.toWalk.append hov.toWalk
  have hl : G.dist u v ≤ 2 := by simpa [p] using G.dist_le p
  have hp : 1 < G.dist u v := p.reachable.one_lt_dist_of_ne_of_not_adj huv hn
  omega

/-- The parallelogram calculation underlying induced-square transport. -/
theorem parallelogram_of_sq_distances (u v w z : E)
    (huv : ‖v - u‖ ^ 2 = 1) (huw : ‖w - u‖ ^ 2 = 1)
    (hvz : ‖z - v‖ ^ 2 = 1) (hwz : ‖z - w‖ ^ 2 = 1)
    (huz : ‖z - u‖ ^ 2 = 2) (hvw : ‖v - w‖ ^ 2 = 2) :
    z = v + w - u := by
  let a := v - u
  let b := w - u
  let c := z - u
  have ha : ‖a‖ ^ 2 = 1 := huv
  have hb : ‖b‖ ^ 2 = 1 := huw
  have hc : ‖c‖ ^ 2 = 2 := huz
  have hab : ‖a - b‖ ^ 2 = 2 := by simpa [a, b] using hvw
  have hca : ‖c - a‖ ^ 2 = 1 := by simpa [c, a] using hvz
  have hcb : ‖c - b‖ ^ 2 = 1 := by simpa [c, b] using hwz
  have iab : ⟪a, b⟫_ℝ = 0 := by
    rw [norm_sub_sq_real] at hab
    linarith
  have ica : ⟪c, a⟫_ℝ = 1 := by
    rw [norm_sub_sq_real] at hca
    linarith
  have icb : ⟪c, b⟫_ℝ = 1 := by
    rw [norm_sub_sq_real] at hcb
    linarith
  have hn : ‖c - (a + b)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, norm_add_sq_real, inner_add_right]
    rw [ha, hb, hc, iab, ica, icb]
    norm_num
  have heq : c = a + b := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  dsimp [a, b, c] at heq
  calc
    z = (z - u) + u := by abel
    _ = ((v - u) + (w - u)) + u := by rw [heq]
    _ = v + w - u := by abel

/-- An induced four-cycle is realized as a parallelogram. -/
theorem induced_square_parallelogram (hf : IsSquaredDistanceEmbedding G f)
    {u v w z : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvz : G.Adj v z) (hwz : G.Adj w z)
    (huz : u ≠ z) (hvw : v ≠ w) (hnuz : ¬G.Adj u z) (hnvw : ¬G.Adj v w) :
    f z = f v + f w - f u := by
  apply parallelogram_of_sq_distances
  · simpa [hf, G.dist_eq_one_iff_adj.mpr huv.symm] using hf v u
  · simpa [G.dist_eq_one_iff_adj.mpr huw.symm] using hf w u
  · simpa [G.dist_eq_one_iff_adj.mpr hvz.symm] using hf z v
  · simpa [G.dist_eq_one_iff_adj.mpr hwz.symm] using hf z w
  · rw [hf, G.dist_comm]
    exact_mod_cast dist_eq_two_of_common_neighbor huz hnuz huv.symm hvz
  · rw [hf]
    exact_mod_cast dist_eq_two_of_common_neighbor hvw hnvw huv huw

/-- The local distance-two condition completes a corner to a unique induced square. -/
theorem exists_unique_square (h2 : TwoCommonNeighbors G)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : v ≠ w) (hnvw : ¬G.Adj v w) :
    ∃! z, G.Adj v z ∧ G.Adj w z ∧ z ≠ u ∧ ¬G.Adj u z := by
  obtain ⟨a, b, hab, hnab, hs⟩ := h2 v w
    (dist_eq_two_of_common_neighbor hvw hnvw huv huw)
  have hu : u = a ∨ u = b := (hs u).mp ⟨huv.symm, huw.symm⟩
  rcases hu with rfl | rfl
  · refine ⟨b, ⟨((hs b).mpr (Or.inr rfl)).1, ((hs b).mpr (Or.inr rfl)).2,
      hab.symm, hnab⟩, ?_⟩
    intro z hz
    exact ((hs z).mp ⟨hz.1, hz.2.1⟩).resolve_left hz.2.2.1
  · refine ⟨a, ⟨((hs a).mpr (Or.inl rfl)).1, ((hs a).mpr (Or.inl rfl)).2,
      hab, fun h => hnab h.symm⟩, ?_⟩
    intro z hz
    exact ((hs z).mp ⟨hz.1, hz.2.1⟩).resolve_right hz.2.2.1

/-- Neighbors at one endpoint outside the clique containing the given edge. -/
abbrev ExternalNeighbors (G : SimpleGraph V) (u v : V) :=
  {w : V // G.Adj u w ∧ w ≠ v ∧ ¬G.Adj v w}

/-- Every external neighbor has a unique translated partner at the other endpoint. -/
theorem exists_external_translation (hf : IsSquaredDistanceEmbedding G f)
    (h2 : TwoCommonNeighbors G) {u v : V} (huv : G.Adj u v)
    (w : ExternalNeighbors G u v) :
    ∃ z : ExternalNeighbors G v u, f z - f v = f w - f u := by
  obtain ⟨z, hz, _⟩ := exists_unique_square h2 huv w.property.1
    w.property.2.1.symm w.property.2.2
  refine ⟨⟨z, hz.1, hz.2.2.1, hz.2.2.2⟩, ?_⟩
  have hp := induced_square_parallelogram hf huv w.property.1 hz.1 hz.2.1
    hz.2.2.1.symm w.property.2.1.symm hz.2.2.2 w.property.2.2
  change f z - f v = f w - f u
  rw [hp]
  abel

/-- The local-square correspondence is an equivalence of the entire external neighborhoods. -/
def externalNeighborEquiv (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) {u v : V} (huv : G.Adj u v) :
    ExternalNeighbors G u v ≃ ExternalNeighbors G v u where
  toFun w := (exists_external_translation hf h2 huv w).choose
  invFun z := (exists_external_translation hf h2 huv.symm z).choose
  left_inv w := by
    apply Subtype.ext
    apply hf.injective hG
    have h := (exists_external_translation hf h2 huv w).choose_spec
    have h' := (exists_external_translation hf h2 huv.symm
      (exists_external_translation hf h2 huv w).choose).choose_spec
    have hh : f ((exists_external_translation hf h2 huv.symm
        (exists_external_translation hf h2 huv w).choose).choose) - f u = f w - f u :=
      h'.trans h
    exact sub_left_injective hh
  right_inv z := by
    apply Subtype.ext
    apply hf.injective hG
    have h := (exists_external_translation hf h2 huv.symm z).choose_spec
    have h' := (exists_external_translation hf h2 huv
      (exists_external_translation hf h2 huv.symm z).choose).choose_spec
    have hh : f ((exists_external_translation hf h2 huv
        (exists_external_translation hf h2 huv.symm z).choose).choose) - f v = f z - f v :=
      h'.trans h
    exact sub_left_injective hh

theorem externalNeighborEquiv_translation (hf : IsSquaredDistanceEmbedding G f)
    (hG : G.Connected) (h2 : TwoCommonNeighbors G) {u v : V} (huv : G.Adj u v)
    (w : ExternalNeighbors G u v) :
    f (externalNeighborEquiv hf hG h2 huv w) - f v = f w - f u :=
  (exists_external_translation hf h2 huv w).choose_spec

omit [InnerProductSpace ℝ E] in
/-- Adjacency can be read directly from the Euclidean realization. -/
theorem IsSquaredDistanceEmbedding.adj_iff (hf : IsSquaredDistanceEmbedding G f)
    (u v : V) : G.Adj u v ↔ ‖f u - f v‖ ^ 2 = 1 := by
  rw [hf, ← G.dist_eq_one_iff_adj]
  norm_cast

omit [InnerProductSpace ℝ E] in
/-- Translated pairs have the same adjacency relation. -/
theorem adj_iff_of_equal_displacement (hf : IsSquaredDistanceEmbedding G f)
    {u v u' v' : V} (h : f u' - f v' = f u - f v) :
    G.Adj u' v' ↔ G.Adj u v := by
  rw [hf.adj_iff, hf.adj_iff, h]

/-- The canonical clique of an edge, including its two endpoints. -/
def edgeClique (G : SimpleGraph V) (u v : V) : Set V :=
  {w | w = u ∨ w = v ∨ (G.Adj u w ∧ G.Adj v w)}

@[simp] theorem left_mem_edgeClique (u v : V) : u ∈ edgeClique G u v := Or.inl rfl
@[simp] theorem right_mem_edgeClique (u v : V) : v ∈ edgeClique G u v := Or.inr (Or.inl rfl)

theorem edgeClique_symm (u v : V) : edgeClique G u v = edgeClique G v u := by
  ext w
  simp only [edgeClique, Set.mem_setOf_eq]
  tauto

/-- Local neighborhood-clique structure makes the canonical edge clique a clique. -/
theorem edgeClique_isClique (hn : NeighborhoodCliques G) {u v : V} (huv : G.Adj u v) :
    G.IsClique (edgeClique G u v) := by
  intro x hx y hy hxy
  rcases hx with rfl | rfl | ⟨hux, hvx⟩
  · rcases hy with rfl | rfl | ⟨huy, _⟩
    · exact (hxy rfl).elim
    · exact huv
    · exact huy
  · rcases hy with rfl | rfl | ⟨_, hvy⟩
    · exact huv.symm
    · exact (hxy rfl).elim
    · exact hvy
  · rcases hy with rfl | rfl | ⟨huy, hvy⟩
    · exact hux.symm
    · exact hvx.symm
    · exact (hn u x v y hux huv huy hvx.symm hvy).resolve_left hxy

/-- Every clique containing an edge lies in its canonical edge clique. -/
theorem clique_subset_edgeClique {C : Set V} (hC : G.IsClique C) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C ⊆ edgeClique G u v := by
  intro w hw
  by_cases hwu : w = u
  · exact Or.inl hwu
  by_cases hwv : w = v
  · exact Or.inr (Or.inl hwv)
  exact Or.inr (Or.inr ⟨hC hu hw (Ne.symm hwu), hC hv hw (Ne.symm hwv)⟩)

/-- Each edge belongs to precisely this maximal clique. -/
theorem edgeClique_maximal (hn : NeighborhoodCliques G) {u v : V} (huv : G.Adj u v) :
    Maximal G.IsClique (edgeClique G u v) := by
  refine ⟨edgeClique_isClique hn huv, ?_⟩
  intro C hC hsub
  exact clique_subset_edgeClique hC (hsub (left_mem_edgeClique u v))
    (hsub (right_mem_edgeClique u v))

theorem maximalClique_eq_edgeClique (hn : NeighborhoodCliques G) {C : Set V}
    (hC : Maximal G.IsClique C) {u v : V} (hu : u ∈ C) (hv : v ∈ C)
    (huv : G.Adj u v) : C = edgeClique G u v := by
  exact Set.Subset.antisymm (clique_subset_edgeClique hC.1 hu hv)
    (hC.2 (edgeClique_isClique hn huv) (clique_subset_edgeClique hC.1 hu hv))

/-- The remaining vertices in another edge clique are all external neighbors. -/
theorem edgeClique_external (hn : NeighborhoodCliques G) {u v w x : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hwv : w ≠ v) (hnvw : ¬G.Adj v w)
    (hx : x ∈ edgeClique G u w) (hxu : x ≠ u) :
    G.Adj u x ∧ x ≠ v ∧ ¬ G.Adj v x := by
  have hux : G.Adj u x := (edgeClique_isClique hn huw) (left_mem_edgeClique u w) hx hxu.symm
  have hxv : x ≠ v := by
    intro heq
    subst x
    rcases hx with h | h | h
    · exact huv.ne h.symm
    · exact hwv h.symm
    · exact hnvw h.2.symm
  refine ⟨hux, hxv, ?_⟩
  intro hvx
  by_cases hxw : x = w
  · exact hnvw (hxw ▸ hvx)
  have hxw' : G.Adj x w := (edgeClique_isClique hn huw) hx (right_mem_edgeClique u w) hxw
  exact ((hn u v x w huv hux huw hvx hxw').resolve_left hwv.symm) |> hnvw

/-- Distinct cliques at a vertex have orthogonal edge directions. -/
theorem external_directions_orthogonal (hf : IsSquaredDistanceEmbedding G f)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : v ≠ w) (hnvw : ¬G.Adj v w) :
    ⟪f v - f u, f w - f u⟫_ℝ = 0 := by
  have hv : ‖f v - f u‖ ^ 2 = 1 := (hf.adj_iff v u).mp huv.symm
  have hw : ‖f w - f u‖ ^ 2 = 1 := (hf.adj_iff w u).mp huw.symm
  have hd : ‖(f v - f u) - (f w - f u)‖ ^ 2 = 2 := by
    rw [sub_sub_sub_cancel_right, hf]
    exact_mod_cast dist_eq_two_of_common_neighbor hvw hnvw huv huw
  rw [norm_sub_sq_real, hv, hw] at hd
  linarith

/-- Every point of another edge clique translates into the corresponding edge clique. -/
theorem edgeClique_translation_exists (hf : IsSquaredDistanceEmbedding G f)
    (hG : G.Connected) (hn : NeighborhoodCliques G) (h2 : TwoCommonNeighbors G)
    {u v w z : V} (huv : G.Adj u v)
    (hw : G.Adj u w ∧ w ≠ v ∧ ¬G.Adj v w)
    (_hz : G.Adj v z ∧ z ≠ u ∧ ¬G.Adj u z)
    (htrans : f z - f v = f w - f u) :
    ∀ x ∈ edgeClique G u w, ∃ y ∈ edgeClique G v z, f y - f v = f x - f u := by
  intro x hx
  by_cases hxu : x = u
  · subst x
    exact ⟨v, left_mem_edgeClique v z, by simp⟩
  have hext := edgeClique_external hn huv hw.1 hw.2.1 hw.2.2 hx hxu
  obtain ⟨y, hy⟩ := exists_external_translation hf h2 huv ⟨x, hext⟩
  refine ⟨y, ?_, hy⟩
  by_cases hxw : x = w
  · have hyy : (y : V) = z := by
      apply hf.injective hG
      apply sub_left_injective (b := f v)
      exact hy.trans ((congrArg (fun t => f t - f u) hxw).trans htrans.symm)
    exact Or.inr (Or.inl hyy)
  · have hxw' : G.Adj x w :=
      (edgeClique_isClique hn hw.1) hx (right_mem_edgeClique u w) hxw
    have hdisp : f y - f z = f x - f w := by
      calc
        f y - f z = (f y - f v) - (f z - f v) := by abel
        _ = (f x - f u) - (f w - f u) := by rw [hy, htrans]
        _ = f x - f w := by abel
    exact Or.inr (Or.inr ⟨y.property.1,
      ((adj_iff_of_equal_displacement hf hdisp).mpr hxw').symm⟩)

/-- Local squares translate an entire maximal clique, with no extra or missing vertices. -/
theorem edgeClique_image_translation (hf : IsSquaredDistanceEmbedding G f)
    (hG : G.Connected) (hn : NeighborhoodCliques G) (h2 : TwoCommonNeighbors G)
    {u v w z : V} (huv : G.Adj u v)
    (hw : G.Adj u w ∧ w ≠ v ∧ ¬G.Adj v w)
    (hz : G.Adj v z ∧ z ≠ u ∧ ¬G.Adj u z)
    (htrans : f z - f v = f w - f u) :
    f '' edgeClique G v z = (fun x => f x + f v - f u) '' edgeClique G u w := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := edgeClique_translation_exists hf hG hn h2 huv.symm
      hz hw htrans.symm y hy
    refine ⟨x, hx, ?_⟩
    calc
      f x + f v - f u = (f x - f u) + f v := by abel
      _ = (f y - f v) + f v := by rw [hxy]
      _ = f y := by abel
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := edgeClique_translation_exists hf hG hn h2 huv
      hw hz htrans x hx
    refine ⟨y, hy, ?_⟩
    calc
      f y = (f y - f v) + f v := by abel
      _ = (f x - f u) + f v := by rw [hyx]
      _ = f x + f v - f u := by abel

/-- The nontrivial maximal cliques at a chosen base vertex, with no repetitions. -/
abbrev BaseClique (G : SimpleGraph V) (o : V) :=
  {C : Set V // ∃ v, G.Adj o v ∧ C = edgeClique G o v}

theorem BaseClique.base_mem {o : V} (C : BaseClique G o) : o ∈ (C : Set V) := by
  obtain ⟨v, _, hC⟩ := C.property
  rw [hC]
  exact left_mem_edgeClique o v

theorem BaseClique.isClique (hn : NeighborhoodCliques G) {o : V} (C : BaseClique G o) :
    G.IsClique (C : Set V) := by
  obtain ⟨v, hv, hC⟩ := C.property
  rw [hC]
  exact edgeClique_isClique hn hv

theorem BaseClique.maximal (hn : NeighborhoodCliques G) {o : V} (C : BaseClique G o) :
    Maximal G.IsClique (C : Set V) := by
  obtain ⟨v, hv, hC⟩ := C.property
  rw [hC]
  exact edgeClique_maximal hn hv

theorem BaseClique.eq_edgeClique (hn : NeighborhoodCliques G) {o : V}
    (C : BaseClique G o) {v : V} (hv : v ∈ (C : Set V)) (hvo : v ≠ o) :
    (C : Set V) = edgeClique G o v :=
  maximalClique_eq_edgeClique hn (C.maximal hn) C.base_mem hv
    (C.isClique hn C.base_mem hv hvo.symm)

/-- Different base cliques intersect only at their base vertex. -/
theorem BaseClique.eq_of_common_ne_base (hn : NeighborhoodCliques G) {o : V}
    {C D : BaseClique G o} {v : V} (hC : v ∈ (C : Set V))
    (hD : v ∈ (D : Set V)) (hvo : v ≠ o) : C = D := by
  apply Subtype.ext
  exact (C.eq_edgeClique hn hC hvo).trans (D.eq_edgeClique hn hD hvo).symm

/-- Nonbase vertices in distinct base cliques are nonadjacent. -/
theorem BaseClique.not_adj (hn : NeighborhoodCliques G) {o : V}
    {C D : BaseClique G o} (hCD : C ≠ D) {v w : V}
    (hv : v ∈ (C : Set V)) (hw : w ∈ (D : Set V)) (hvo : v ≠ o) (hwo : w ≠ o) :
    ¬ G.Adj v w := by
  intro hvw
  have how : G.Adj o w := D.isClique hn D.base_mem hw hwo.symm
  have hwC : w ∈ (C : Set V) := by
    rw [C.eq_edgeClique hn hv hvo]
    exact Or.inr (Or.inr ⟨how, hvw⟩)
  exact hCD (BaseClique.eq_of_common_ne_base hn hwC hw hwo)

/-- The geometric base factors are pairwise orthogonal, including their zero vertices. -/
theorem BaseClique.orthogonal (hf : IsSquaredDistanceEmbedding G f)
    (hn : NeighborhoodCliques G) {o : V} {C D : BaseClique G o} (hCD : C ≠ D)
    (v : C.val) (w : D.val) : ⟪f v - f o, f w - f o⟫_ℝ = 0 := by
  by_cases hvo : (v : V) = o
  · simp [hvo]
  by_cases hwo : (w : V) = o
  · simp [hwo]
  have hvw : (v : V) ≠ w := by
    intro h
    exact hCD (BaseClique.eq_of_common_ne_base hn v.property (h ▸ w.property) hvo)
  exact external_directions_orthogonal hf
    (C.isClique hn C.base_mem v.property (Ne.symm hvo))
    (D.isClique hn D.base_mem w.property (Ne.symm hwo))
    hvw (BaseClique.not_adj hn hCD v.property w.property hvo hwo)

/-- Each base factor has at least two vertices. -/
theorem BaseClique.card_ge_two [Fintype V] [DecidableEq V] {o : V}
    (C : BaseClique G o) [Fintype C.val] : 2 ≤ Fintype.card C.val := by
  obtain ⟨v, hv, hC⟩ := C.property
  have hvC : v ∈ (C : Set V) := by rw [hC]; exact right_mem_edgeClique o v
  exact Fintype.one_lt_card_iff.mpr ⟨⟨o, C.base_mem⟩, ⟨v, hvC⟩,
    fun h => hv.ne (congrArg Subtype.val h)⟩

section Frames

variable {I : Type*}

/-- A family of unit-side simplexes in pairwise orthogonal subspaces. -/
structure OrthogonalSimplexFamily (S : I → Set E) : Prop where
  zero_mem : ∀ i, 0 ∈ S i
  unit_dist : ∀ i {x y}, x ∈ S i → y ∈ S i → x ≠ y → ‖x - y‖ ^ 2 = 1
  orthogonal : ∀ {i j}, i ≠ j → ∀ {x y}, x ∈ S i → y ∈ S j → ⟪x, y⟫_ℝ = 0

variable {S : I → Set E}

theorem OrthogonalSimplexFamily.differences_orthogonal (hS : OrthogonalSimplexFamily S)
    {i j : I} (hij : i ≠ j) {x x' y y' : E}
    (hx : x ∈ S i) (hx' : x' ∈ S i) (hy : y ∈ S j) (hy' : y' ∈ S j) :
    ⟪x - x', y - y'⟫_ℝ = 0 := by
  simp only [inner_sub_left, inner_sub_right, hS.orthogonal hij hx hy,
    hS.orthogonal hij hx hy', hS.orthogonal hij hx' hy, hS.orthogonal hij hx' hy']
  ring

theorem OrthogonalSimplexFamily.cross_distance (hS : OrthogonalSimplexFamily S)
    {i j : I} (hij : i ≠ j) {x x' y y' : E}
    (hx : x ∈ S i) (hx' : x' ∈ S i) (hy : y ∈ S j) (hy' : y' ∈ S j)
    (hxx' : x ≠ x') (hyy' : y ≠ y') :
    ‖(x - x') - (y - y')‖ ^ 2 = 2 := by
  rw [norm_sub_sq_real, hS.unit_dist i hx hx' hxx', hS.unit_dist j hy hy' hyy',
    hS.differences_orthogonal hij hx hx' hy hy']
  norm_num

/-- Exact description of every neighbor direction, including realization of every
allowed one-coordinate change. -/
def HasFrame (G : SimpleGraph V) (f : V → E) (S : I → Set E) (p : V) (a : I → E) : Prop :=
  ∀ d, (∃ q, G.Adj p q ∧ f q - f p = d) ↔
    ∃ i s, s ∈ S i ∧ s ≠ a i ∧ d = s - a i

/-- Neighbor frames propagate along every edge by changing exactly its coordinate. -/
theorem HasFrame.step [DecidableEq I] (hf : IsSquaredDistanceEmbedding G f)
    (hG : G.Connected) (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {p q : V} {a : I → E} (ha : ∀ i, a i ∈ S i) (hp : HasFrame G f S p a)
    (hpq : G.Adj p q) {i : I} {s : E} (hs : s ∈ S i) (hsa : s ≠ a i)
    (hqp : f q - f p = s - a i) :
    HasFrame G f S q (Function.update a i s) := by
  intro d
  constructor
  · rintro ⟨r, hqr, hrq⟩
    by_cases hrp : r = p
    · subst r
      refine ⟨i, a i, ha i, ?_, ?_⟩
      · simpa using hsa.symm
      · simp only [Function.update_self]
        rw [← hrq]
        calc
          f p - f q = -(f q - f p) := by abel
          _ = -(s - a i) := by rw [hqp]
          _ = a i - s := by abel
    by_cases hpr : G.Adj p r
    · obtain ⟨j, t, ht, hta, hrt⟩ := (hp (f r - f p)).mp ⟨r, hpr, rfl⟩
      have hji : j = i := by
        by_contra hji
        have hd : ‖f r - f q‖ ^ 2 = 2 := by
          have hdisp : f r - f q = (t - a j) - (s - a i) := by
            calc
              f r - f q = (f r - f p) - (f q - f p) := by abel
              _ = (t - a j) - (s - a i) := by rw [hrt, hqp]
          rw [hdisp]
          exact hS.cross_distance hji ht (ha j) hs (ha i) hta hsa
        have hd' := (hf.adj_iff r q).mp hqr.symm
        linarith
      subst j
      have hts : t ≠ s := by
        intro heq
        have hrq' : r = q := by
          apply hf.injective hG
          apply sub_left_injective (b := f p)
          exact hrt.trans ((congrArg (fun t => t - a i) heq).trans hqp.symm)
        exact hqr.ne hrq'.symm
      refine ⟨i, t, ht, by simpa using hts, ?_⟩
      simp only [Function.update_self]
      rw [← hrq]
      calc
        f r - f q = (f r - f p) - (f q - f p) := by abel
        _ = (t - a i) - (s - a i) := by rw [hrt, hqp]
        _ = t - s := by abel
    · obtain ⟨w, hw⟩ := exists_external_translation hf h2 hpq.symm ⟨r, hqr, hrp, hpr⟩
      obtain ⟨j, t, ht, hta, hwt⟩ := (hp (f w - f p)).mp ⟨w, w.property.1, rfl⟩
      have hji : j ≠ i := by
        intro hji
        subst j
        have hts : t ≠ s := by
          intro heq
          have hwq : (w : V) = q := by
            apply hf.injective hG
            apply sub_left_injective (b := f p)
            exact hwt.trans ((congrArg (fun t => t - a i) heq).trans hqp.symm)
          exact w.property.2.1 hwq
        have hqw : G.Adj q w := by
          apply (hf.adj_iff q w).mpr
          have hdisp : f q - f w = s - t := by
            calc
              f q - f w = (f q - f p) - (f w - f p) := by abel
              _ = (s - a i) - (t - a i) := by rw [hqp, hwt]
              _ = s - t := by abel
          rw [hdisp]
          exact hS.unit_dist i hs ht hts.symm
        exact w.property.2.2 hqw
      refine ⟨j, t, ht, ?_, ?_⟩
      · simpa [Function.update_of_ne hji] using hta
      · rw [Function.update_of_ne hji]
        exact hrq.symm.trans (hw.symm.trans hwt)
  · rintro ⟨j, t, ht, hta, hdt⟩
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self] at hta hdt
      by_cases hta' : t = a i
      · refine ⟨p, hpq.symm, ?_⟩
        rw [hdt, hta']
        calc
          f p - f q = -(f q - f p) := by abel
          _ = -(s - a i) := by rw [hqp]
          _ = a i - s := by abel
      · obtain ⟨r, hpr, hrp⟩ := (hp (t - a i)).mpr ⟨i, t, ht, hta', rfl⟩
        have hdisp : f r - f q = t - s := by
          calc
            f r - f q = (f r - f p) - (f q - f p) := by abel
            _ = (t - a i) - (s - a i) := by rw [hrp, hqp]
            _ = t - s := by abel
        refine ⟨r, ?_, hdisp.trans hdt.symm⟩
        apply (hf.adj_iff r q).mpr _ |>.symm
        rw [hdisp]
        exact hS.unit_dist i ht hs hta
    · rw [Function.update_of_ne hji] at hta hdt
      obtain ⟨w, hpw, hwp⟩ := (hp (t - a j)).mpr ⟨j, t, ht, hta, rfl⟩
      have hd : ‖f w - f q‖ ^ 2 = 2 := by
        have hdisp : f w - f q = (t - a j) - (s - a i) := by
          calc
            f w - f q = (f w - f p) - (f q - f p) := by abel
            _ = (t - a j) - (s - a i) := by rw [hwp, hqp]
        rw [hdisp]
        exact hS.cross_distance hji ht (ha j) hs (ha i) hta hsa
      have hwq : w ≠ q := by
        intro heq
        simp [heq] at hd
      have hnqw : ¬ G.Adj q w := by
        intro hqw
        have hd' := (hf.adj_iff w q).mp hqw.symm
        linarith
      obtain ⟨r, hr⟩ := exists_external_translation hf h2 hpq ⟨w, hpw, hwq, hnqw⟩
      exact ⟨r, r.property.1, hr.trans (hwp.trans hdt.symm)⟩

omit [InnerProductSpace ℝ E] in
/-- Updating one coordinate changes the finite sum by exactly its displacement. -/
theorem sum_update_displacement [Fintype I] [DecidableEq I] (a : I → E) (i : I) (s : E) :
    (∑ j, Function.update a i s j) = (∑ j, a j) + (s - a i) := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) a]
  abel

/-- One step also preserves coordinate membership and the represented vector. -/
theorem HasFrame.step_with_sum [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o p q : V} {a : I → E} (ha : ∀ i, a i ∈ S i) (hp : HasFrame G f S p a)
    (hsum : f p - f o = ∑ i, a i) (hpq : G.Adj p q) :
    ∃ b : I → E, (∀ i, b i ∈ S i) ∧ HasFrame G f S q b ∧ f q - f o = ∑ i, b i := by
  obtain ⟨i, s, hs, hsa, hqp⟩ := (hp (f q - f p)).mp ⟨q, hpq, rfl⟩
  refine ⟨Function.update a i s, ?_, hp.step hf hG h2 hS ha hpq hs hsa hqp, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j; simpa
    · simpa [Function.update_of_ne hji] using ha j
  · rw [sum_update_displacement, ← hsum, ← hqp]
    abel

/-- Path induction carries the exact local frame and its coordinate sum to every vertex. -/
theorem HasFrame.exists_at_walk [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o p q : V} (walk : G.Walk p q) {a : I → E}
    (ha : ∀ i, a i ∈ S i) (hp : HasFrame G f S p a)
    (hsum : f p - f o = ∑ i, a i) :
    ∃ b : I → E, (∀ i, b i ∈ S i) ∧ HasFrame G f S q b ∧ f q - f o = ∑ i, b i := by
  induction walk generalizing a with
  | nil => exact ⟨a, ha, hp, hsum⟩
  | @cons p r q hpr walk ih =>
    obtain ⟨b, hb, hframe, hbsum⟩ := hp.step_with_sum hf hG h2 hS ha hsum hpr
    exact ih hb hframe hbsum

/-- Connectedness yields the first inclusion in the Cartesian sum description. -/
theorem HasFrame.exists_at_vertex [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o : V} (ho : HasFrame G f S o (fun _ => 0)) (p : V) :
    ∃ a : I → E, (∀ i, a i ∈ S i) ∧ HasFrame G f S p a ∧ f p - f o = ∑ i, a i := by
  obtain ⟨walk⟩ := hG o p
  exact ho.exists_at_walk hf hG h2 hS walk hS.zero_mem (by simp)

/-- Every permissible coordinate update is realized by a vertex and its exact frame. -/
theorem HasFrame.realizes_update [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o p : V} {a : I → E} (ha : ∀ i, a i ∈ S i) (hp : HasFrame G f S p a)
    (hsum : f p - f o = ∑ i, a i) (i : I) {s : E} (hs : s ∈ S i) :
    ∃ q, HasFrame G f S q (Function.update a i s) ∧
      f q - f o = ∑ j, Function.update a i s j := by
  by_cases hsa : s = a i
  · simpa [hsa, Function.update_eq_self] using (show ∃ q, HasFrame G f S q a ∧
      f q - f o = ∑ j, a j from ⟨p, hp, hsum⟩)
  obtain ⟨q, hpq, hqp⟩ := (hp (s - a i)).mpr ⟨i, s, hs, hsa, rfl⟩
  refine ⟨q, hp.step hf hG h2 hS ha hpq hs hsa hqp, ?_⟩
  rw [sum_update_displacement, ← hsum, ← hqp]
  abel

/-- Changing the finitely many coordinates one by one proves the reverse inclusion. -/
theorem HasFrame.realizes_all_coordinates [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o : V} (ho : HasFrame G f S o (fun _ => 0))
    (a : I → E) (ha : ∀ i, a i ∈ S i) :
    ∃ p, HasFrame G f S p a ∧ f p - f o = ∑ i, a i := by
  classical
  have hind : ∀ F : Finset I, ∃ p,
      HasFrame G f S p (fun i => if i ∈ F then a i else 0) ∧
      f p - f o = ∑ i, (if i ∈ F then a i else 0) := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨o, by simpa using ho, by simp⟩
    | @insert i F hi ih =>
      obtain ⟨p, hp, hsum⟩ := ih
      have hmem : ∀ j, (if j ∈ F then a j else 0) ∈ S j := by
        intro j
        split_ifs
        · exact ha j
        · exact hS.zero_mem j
      obtain ⟨q, hq, hqsum⟩ := hp.realizes_update hf hG h2 hS hmem hsum i (ha i)
      have heq : Function.update (fun j => if j ∈ F then a j else 0) i (a i) =
          (fun j => if j ∈ insert i F then a j else 0) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      exact ⟨q, heq ▸ hq, by simpa only [heq] using hqsum⟩
  simpa using hind Finset.univ

/-- Orthogonality makes the finite coordinate sum injective. -/
theorem OrthogonalSimplexFamily.sum_injective [Fintype I]
    (hS : OrthogonalSimplexFamily S) {a b : I → E}
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ S i)
    (hsum : ∑ i, a i = ∑ i, b i) : a = b := by
  classical
  funext i
  have hz : ∑ j, (a j - b j) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hd : (∑ j, ⟪a j - b j, a i - b i⟫_ℝ) = ⟪a i - b i, a i - b i⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hS.differences_orthogonal hji (ha j) (hb j) (ha i) (hb i)
    · simp
  have hinner := congrArg (fun x => ⟪x, a i - b i⟫_ℝ) hz
  dsimp only at hinner
  rw [sum_inner, hd, inner_zero_left, real_inner_self_eq_norm_sq] at hinner
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hinner))

/-- The dependent Cartesian product of complete graphs: adjacency means exactly
one coordinate differs. Its factors are the complete graphs on the types `A i`. -/
def hammingGraph (A : I → Type*) : SimpleGraph (∀ i, A i) where
  Adj a b := ∃ i, a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j
  symm := by
    rintro a b ⟨i, hi, hrest⟩
    exact ⟨i, hi.symm, fun j hj => (hrest j hj).symm⟩
  loopless := by
    intro a h
    obtain ⟨i, hi, _⟩ := h
    exact hi rfl

/-- Exact frames on an orthogonal simplex family give an actual graph isomorphism. -/
theorem HasFrame.hamming_isomorphism [Fintype I] [DecidableEq I]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (h2 : TwoCommonNeighbors G) (hS : OrthogonalSimplexFamily S)
    {o : V} (ho : HasFrame G f S o (fun _ => 0)) :
    Nonempty (hammingGraph (fun i => S i) ≃g G) := by
  classical
  let F : (∀ i, S i) → V := fun a =>
    (ho.realizes_all_coordinates hf hG h2 hS (fun i => a i) (fun i => (a i).property)).choose
  have hF (a : ∀ i, S i) : HasFrame G f S (F a) (fun i => a i) ∧
      f (F a) - f o = ∑ i, (a i : E) :=
    (ho.realizes_all_coordinates hf hG h2 hS (fun i => a i) (fun i => (a i).property)).choose_spec
  have hFinj : Function.Injective F := by
    intro a b hab
    have heq : (fun i => (a i : E)) = (fun i => (b i : E)) := by
      apply hS.sum_injective (fun i => (a i).property) (fun i => (b i).property)
      rw [← (hF a).2, ← (hF b).2, hab]
    funext i
    exact Subtype.ext (congrFun heq i)
  have hFsur : Function.Surjective F := by
    intro p
    obtain ⟨a, ha, _, hsum⟩ := ho.exists_at_vertex hf hG h2 hS p
    refine ⟨fun i => ⟨a i, ha i⟩, ?_⟩
    apply hf.injective hG
    apply sub_left_injective (b := f o)
    exact (hF _).2.trans hsum.symm
  let e : (∀ i, S i) ≃ V := Equiv.ofBijective F ⟨hFinj, hFsur⟩
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro a b
  change G.Adj (F a) (F b) ↔ ∃ i, a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j
  constructor
  · intro hab
    obtain ⟨i, s, hs, hsa, hdisp⟩ := ((hF a).1 (f (F b) - f (F a))).mp ⟨F b, hab, rfl⟩
    have hmem : ∀ j, Function.update (fun k => (a k : E)) i s j ∈ S j := by
      intro j
      by_cases hji : j = i
      · subst j; simpa
      · simp [Function.update_of_ne hji]
    have hsum : (∑ j, (b j : E)) = ∑ j, Function.update (fun k => (a k : E)) i s j := by
      rw [sum_update_displacement, ← (hF a).2, ← (hF b).2, ← hdisp]
      abel
    have heq := hS.sum_injective (fun j => (b j).property) hmem hsum
    refine ⟨i, ?_, ?_⟩
    · intro hai
      have hbi : (b i : E) = s := by simpa using congrFun heq i
      exact hsa (hbi.symm.trans (congrArg Subtype.val hai).symm)
    · intro j hji
      apply Subtype.ext
      simpa [Function.update_of_ne hji] using (congrFun heq j).symm
  · rintro ⟨i, hai, hrest⟩
    have hdisp : f (F a) - f (F b) = (a i : E) - (b i : E) := by
      calc
        f (F a) - f (F b) = (f (F a) - f o) - (f (F b) - f o) := by abel
        _ = (∑ j, (a j : E)) - ∑ j, (b j : E) := by rw [(hF a).2, (hF b).2]
        _ = ∑ j, ((a j : E) - (b j : E)) := by rw [Finset.sum_sub_distrib]
        _ = (a i : E) - (b i : E) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            rw [hrest j hji, sub_self]
          · simp
    apply (hf.adj_iff (F a) (F b)).mpr
    rw [hdisp]
    exact hS.unit_dist i (a i).property (b i).property (fun h => hai (Subtype.ext h))

end Frames

/-- The simplex belonging to a base clique, translated to contain zero. -/
def baseSimplex (f : V → E) (o : V) (C : BaseClique G o) : Set E :=
  (fun v => f v - f o) '' (C : Set V)

theorem baseSimplex_family (hf : IsSquaredDistanceEmbedding G f)
    (hn : NeighborhoodCliques G) (o : V) : OrthogonalSimplexFamily (baseSimplex (G := G) f o) where
  zero_mem C := ⟨o, C.base_mem, by simp⟩
  unit_dist C := by
    rintro x y ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ hne
    have hvw : v ≠ w := fun h => hne (congrArg (fun z => f z - f o) h)
    rw [sub_sub_sub_cancel_right]
    exact (hf.adj_iff v w).mp (C.isClique hn hv hw hvw)
  orthogonal := by
    intro C D hCD x y hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact BaseClique.orthogonal hf hn hCD ⟨v, hv⟩ ⟨w, hw⟩

omit [InnerProductSpace ℝ E] in
/-- The base cliques give the initial exact neighbor frame. -/
theorem hasFrame_base (hf : IsSquaredDistanceEmbedding G f)
    (hn : NeighborhoodCliques G) (o : V) :
    HasFrame G f (baseSimplex (G := G) f o) o (fun _ => 0) := by
  intro d
  constructor
  · rintro ⟨v, hov, rfl⟩
    let C : BaseClique G o := ⟨edgeClique G o v, v, hov, rfl⟩
    refine ⟨C, f v - f o, ⟨v, right_mem_edgeClique o v, rfl⟩, ?_, by simp⟩
    intro hzero
    have hnorm := (hf.adj_iff v o).mp hov.symm
    rw [hzero] at hnorm
    norm_num at hnorm
  · rintro ⟨C, s, ⟨v, hv, rfl⟩, hne, hd⟩
    have hvo : v ≠ o := by rintro rfl; exact hne (sub_self _)
    exact ⟨v, C.isClique hn C.base_mem hv hvo.symm, by simpa using hd.symm⟩


/-- Replacing each complete-graph factor by an equivalent vertex type preserves the product. -/
def hammingGraph_congr {I : Type*} {A B : I → Type*} (e : ∀ i, A i ≃ B i) :
    hammingGraph A ≃g hammingGraph B where
  toEquiv := Equiv.piCongrRight e
  map_rel_iff' := by
    intro a b
    change (∃ i, e i (a i) ≠ e i (b i) ∧ ∀ j, j ≠ i → e j (a j) = e j (b j)) ↔
      ∃ i, a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j
    constructor
    · rintro ⟨i, hi, hrest⟩
      exact ⟨i, fun h => hi (congrArg (e i) h), fun j hj => (e j).injective (hrest j hj)⟩
    · rintro ⟨i, hi, hrest⟩
      exact ⟨i, fun h => hi ((e i).injective h), fun j hj => congrArg (e j) (hrest j hj)⟩

/-- Reindexing the factors preserves the dependent Cartesian product. -/
def hammingGraph_reindex {I J : Type*} (e : I ≃ J) (A : I → Type*) :
    hammingGraph A ≃g hammingGraph (fun j => A (e.symm j)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_rel_iff' := by
    intro a b
    change (∃ j, a (e.symm j) ≠ b (e.symm j) ∧
      ∀ k, k ≠ j → a (e.symm k) = b (e.symm k)) ↔
      ∃ i, a i ≠ b i ∧ ∀ k, k ≠ i → a k = b k
    constructor
    · rintro ⟨j, hj, hrest⟩
      refine ⟨e.symm j, hj, ?_⟩
      intro k hk
      have hkj : e k ≠ j := fun h => hk (by simpa using congrArg e.symm h)
      exact Eq.mp (congrArg (fun t : I => a t = b t) (e.symm_apply_apply k))
        (hrest (e k) hkj)
    · rintro ⟨i, hi, hrest⟩
      refine ⟨e i, Eq.mpr (congrArg (fun t : I => a t ≠ b t) (e.symm_apply_apply i)) hi, ?_⟩
      intro k hk
      have hki : e.symm k ≠ i := fun h => hk (by simpa using congrArg e h)
      exact hrest (e.symm k) hki

/-- Each geometric base simplex is equivalent to its original graph clique. -/
def baseSimplex_equiv (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (o : V) (C : BaseClique G o) : C.val ≃ baseSimplex f o C :=
  Equiv.ofBijective (fun v => ⟨f v - f o, ⟨v, v.property, rfl⟩⟩) (by
    constructor
    · intro v w h
      apply Subtype.ext
      apply hf.injective hG
      exact sub_left_injective (congrArg Subtype.val h)
    · rintro ⟨x, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩)

/-- The geometric part of Lemma 4.6: the graph is the Cartesian product of its
nontrivial base cliques. The product has no factors when the graph has one vertex. -/
theorem cartesian_isomorphism [Fintype V] [DecidableEq V]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (hn : NeighborhoodCliques G) (h2 : TwoCommonNeighbors G) (o : V) :
    Nonempty (G ≃g hammingGraph (fun C : BaseClique G o => C.val)) := by
  classical
  letI : Fintype (BaseClique G o) := Fintype.ofFinite _
  obtain ⟨e⟩ := (hasFrame_base hf hn o).hamming_isomorphism hf hG h2
    (baseSimplex_family hf hn o)
  exact ⟨e.symm.trans (hammingGraph_congr (baseSimplex_equiv hf hG o)).symm⟩

/-- A numerical factor-size formulation of the Cartesian product characterization.
`hammingGraph (fun i => Fin (s i))` is `K_(s 0) □ ... □ K_(s (d-1))`.
For `d = 0` its vertex type is the one-element empty dependent product. -/
theorem exists_complete_factors [Fintype V] [DecidableEq V]
    (hf : IsSquaredDistanceEmbedding G f) (hG : G.Connected)
    (hn : NeighborhoodCliques G) (h2 : TwoCommonNeighbors G) :
    ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
      Nonempty (G ≃g hammingGraph (fun i => Fin (s i))) := by
  classical
  let o : V := hG.nonempty.some
  letI : Fintype (BaseClique G o) := Fintype.ofFinite _
  letI (C : BaseClique G o) : Fintype C.val := Fintype.ofFinite _
  let eI := Fintype.equivFin (BaseClique G o)
  let s : Fin (Fintype.card (BaseClique G o)) → ℕ := fun i => Fintype.card (eI.symm i).val
  refine ⟨Fintype.card (BaseClique G o), s, ?_, ?_⟩
  · intro i
    exact (eI.symm i).card_ge_two
  · obtain ⟨e⟩ := cartesian_isomorphism hf hG hn h2 o
    exact ⟨(e.trans (hammingGraph_reindex eI (fun C : BaseClique G o => C.val))).trans
      (hammingGraph_congr (fun i => Fintype.equivFin (eI.symm i).val))⟩

/-- Lemma 4.6 in full: PSD graph-distance kernels and the two local graph
conditions force a finite Cartesian product of complete graphs, each of size at least two. -/
theorem cartesian_product_characterization [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hpsd : ∀ x : ℝ, 0 < x → x < 1 → (EntropyCompletion.distanceKernel G x).PosSemidef)
    (hn : NeighborhoodCliques G) (h2 : TwoCommonNeighbors G) :
    ∃ d : ℕ, ∃ s : Fin d → ℕ, (∀ i, 2 ≤ s i) ∧
      Nonempty (G ≃g hammingGraph (fun i => Fin (s i))) := by
  obtain ⟨f, _, hf⟩ := EntropyCompletion.exists_distance_embedding G hG hpsd
  exact exists_complete_factors (f := f) hf hG hn h2

/-- The common-neighbor condition itself rules out an induced length-two path
inside a neighborhood, hence implies the neighborhood-clique condition. -/
theorem TwoCommonNeighbors.neighborhoodCliques (h2 : TwoCommonNeighbors G) :
    NeighborhoodCliques G := by
  intro o u v w hou hov how huv hvw
  by_cases huw : u = w
  · exact Or.inl huw
  by_cases hadj : G.Adj u w
  · exact Or.inr hadj
  obtain ⟨a, b, _, hnab, hs⟩ := h2 u w (dist_eq_two_of_common_neighbor huw hadj hou how)
  have ho : o = a ∨ o = b := (hs o).mp ⟨hou.symm, how.symm⟩
  have hv : v = a ∨ v = b := (hs v).mp ⟨huv, hvw.symm⟩
  rcases ho with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hov.ne rfl).elim
  · exact (hnab hov).elim
  · exact (hnab hov.symm).elim
  · exact (hov.ne rfl).elim

/-- Splitting off the first coordinate is exactly a Cartesian (box) product
with a complete graph. This identifies the dependent Hamming definition with
the iterated Cartesian product used in the paper. -/
def hammingGraph_finSucc {n : ℕ} (A : Fin (n + 1) → Type*) :
    hammingGraph A ≃g (⊤ : SimpleGraph (A 0)) □ hammingGraph (fun i : Fin n => A i.succ) where
  toEquiv := (Fin.consEquiv A).symm
  map_rel_iff' := by
    intro a b
    change ((a 0 ≠ b 0 ∧ (fun i : Fin n => a i.succ) = (fun i : Fin n => b i.succ)) ∨
      ((∃ i : Fin n, a i.succ ≠ b i.succ ∧ ∀ j, j ≠ i → a j.succ = b j.succ) ∧
        a 0 = b 0)) ↔
      ∃ i : Fin (n + 1), a i ≠ b i ∧ ∀ j, j ≠ i → a j = b j
    constructor
    · rintro (⟨hzero, htail⟩ | ⟨⟨i, hi, hrest⟩, hzero⟩)
      · refine ⟨0, hzero, ?_⟩
        intro j hj
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
        · exact (hj rfl).elim
        · exact congrFun htail k
      · refine ⟨i.succ, hi, ?_⟩
        intro j hj
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
        · exact hzero
        · exact hrest k (fun h => hj (congrArg Fin.succ h))
    · rintro ⟨i, hi, hrest⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · exact Or.inl ⟨hi, funext (fun j => hrest j.succ (Fin.succ_ne_zero j))⟩
      · exact Or.inr ⟨⟨k, hi, fun j hj => hrest j.succ (fun h => hj (Fin.succ_injective _ h))⟩,
          hrest 0 (Fin.succ_ne_zero k).symm⟩

/-- The empty Cartesian product is the one-vertex complete graph. -/
def hammingGraph_finZero (A : Fin 0 → Type*) :
    hammingGraph A ≃g (⊤ : SimpleGraph (Fin 1)) where
  toEquiv := Equiv.ofUnique _ _
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact (h (Subsingleton.elim _ _)).elim
    · rintro ⟨i, _, _⟩
      exact Fin.elim0 i

end PlanarHom.CartesianGeometry
