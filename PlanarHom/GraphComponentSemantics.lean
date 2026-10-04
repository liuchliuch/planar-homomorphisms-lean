import PlanarHom.GraphComponentDecomposition
import PlanarHom.MixedTotalEvaluation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact partition factorization over the component codes computed by the
occurrence-list machine. Every occurrence and isolated vertex is retained. -/
noncomputable section
open scoped BigOperators
open Classical

namespace PlanarHom.GraphComponentCode
open Complexity

abbrev PartIndex (g : MixedCode) := Fin (parts g).length
abbrev PartVertex (g : MixedCode) (p : PartIndex g) := Fin ((parts g).get p).length

/-- The original vertex represented by a local position in a computed part. -/
def partVertex (g : MixedCode) (p : PartIndex g) (v : PartVertex g p) : Fin g.vertices :=
  ⟨((parts g).get p).get v,
    part_vertex_lt g _ (List.get_mem _ _) _ (List.get_mem _ _)⟩

theorem partVertex_bijective (g : MixedCode) :
    Function.Bijective (fun v : Σ p : PartIndex g, PartVertex g p => partVertex g v.1 v.2) := by
  constructor
  · rintro ⟨p,u⟩ ⟨q,v⟩ h
    have hv := congrArg Fin.val h
    change ((parts g).get p).get u = ((parts g).get q).get v at hv
    have hpq : p=q := (parts_nodup g).get_inj_iff.mp
      (part_eq_of_common g _ _ (List.get_mem _ _) (List.get_mem _ _)
        (((parts g).get p).get u) (List.get_mem _ _) (hv.symm ▸ List.get_mem _ _))
    subst q
    have huv : u=v := (part_nodup g _ (List.get_mem _ _)).get_inj_iff.mp hv
    subst v
    rfl
  · intro v
    obtain ⟨xs,hxs,hv⟩ := vertex_mem_part g v.val v.isLt
    obtain ⟨p,rfl⟩ := List.mem_iff_get.mp hxs
    obtain ⟨u,hu⟩ := List.mem_iff_get.mp hv
    exact ⟨⟨p,u⟩,Fin.ext hu⟩

/-- A concrete local-position representation of all original vertices. -/
def partVertexEquiv (g : MixedCode) :
    (Σ p : PartIndex g, PartVertex g p) ≃ Fin g.vertices :=
  Equiv.ofBijective _ (partVertex_bijective g)

/-- Restrict a global coloring to the computed components. The inverse joins
the local colorings through the proved vertex bijection. -/
def componentColoringEquiv (g : MixedCode) (C : Type*) :
    (Fin g.vertices → C) ≃ (∀ p : PartIndex g, PartVertex g p → C) where
  toFun σ p v := σ (partVertex g p v)
  invFun τ v := τ ((partVertexEquiv g).symm v).1 ((partVertexEquiv g).symm v).2
  left_inv σ := by
    funext v
    exact congrArg σ ((partVertexEquiv g).apply_symm_apply v)
  right_inv τ := by
    funext p v
    change τ ((partVertexEquiv g).symm ((partVertexEquiv g) ⟨p,v⟩)).1
      ((partVertexEquiv g).symm ((partVertexEquiv g) ⟨p,v⟩)).2 = τ p v
    rw [Equiv.symm_apply_apply]

theorem background_factorization {C R : Type*} [CommMonoid R]
    (g : MixedCode) (w : C → R) (σ : Fin g.vertices → C) :
    (∏ p : PartIndex g, ∏ v : PartVertex g p, w (σ (partVertex g p v))) =
      ∏ v, w (σ v) := by
  calc
    _ = ∏ x : (Σ p : PartIndex g, PartVertex g p), w (σ (partVertex g x.1 x.2)) :=
      (Fintype.prod_sigma _).symm
    _ = _ := Fintype.prod_equiv (partVertexEquiv g) _ _ (fun _ => rfl)

/-- Partitioning a list of occurrences by a unique finite owner preserves its
product, even when equal values occur several times. -/
theorem prod_filtered_partition {I A R : Type*} [Fintype I] [CommMonoid R]
    (es : List A) (P : I → A → Prop) [DecidableRel P] (f : A → R)
    (hP : ∀ a∈es, ∃! i, P i a) :
    (∏ i, ((es.filter (fun a => decide (P i a))).map f).prod) = (es.map f).prod := by
  induction es with
  | nil => simp
  | cons a es ih =>
    obtain ⟨i,hi,huniq⟩ := hP a (by simp)
    have hiff (j : I) : P j a ↔ j=i := ⟨fun h => huniq j h, fun h => h ▸ hi⟩
    have ht := ih (fun b hb => hP b (by simp [hb]))
    simp only [List.filter_cons, List.map_cons, List.prod_cons]
    simp_rw [hiff]
    have he (j : I) :
        ((if decide (j=i) then a :: es.filter (fun a => decide (P j a))
          else es.filter (fun a => decide (P j a))).map f).prod =
          (if j=i then f a else 1) * ((es.filter (fun a => decide (P j a))).map f).prod := by
      by_cases h : j=i <;> simp [h]
    simp_rw [he]
    rw [Finset.prod_mul_distrib, ht]
    simp

theorem vertex_unique_part (g : MixedCode) (v : ℕ) (hv : v<g.vertices) :
    ∃! p : PartIndex g, v∈(parts g).get p := by
  obtain ⟨xs,hxs,hv⟩ := vertex_mem_part g v hv
  obtain ⟨p,rfl⟩ := List.mem_iff_get.mp hxs
  refine ⟨p,hv,?_⟩
  intro q hq
  exact (parts_nodup g).get_inj_iff.mp
    (part_eq_of_common g _ _ (List.get_mem _ _) (List.get_mem _ _) v hq hv)

theorem edge_unique_part {b u : ℕ} (g : MixedCode) (hg : g.Valid b u)
    (e : Edge) (he : e∈g.edges) :
    ∃! p : PartIndex g, e.1∈(parts g).get p ∧ e.2.1∈(parts g).get p := by
  obtain ⟨p,hp,hu⟩ := vertex_unique_part g e.1 (hg.1 e he).1
  exact ⟨p,⟨hp,(part_edge_closed g hg _ (List.get_mem _ _) e he).mp hp⟩,
    fun q hq => hu q hq.1⟩

@[simp] theorem partVertex_idxOf (g : MixedCode) (p : PartIndex g) (v : ℕ)
    (hv : v∈(parts g).get p) (hlt : v<g.vertices) :
    partVertex g p ⟨((parts g).get p).idxOf v,List.idxOf_lt_length_iff.mpr hv⟩ =
      ⟨v,hlt⟩ := by
  apply Fin.ext
  simp [partVertex]

theorem extracted_binaryValue {C R : Type} [One R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (p : PartIndex g)
    (σ : Fin g.vertices → C) (M : Fin b → Matrix C C R)
    (e : Edge) (he : e∈g.edges)
    (hmem : e.1∈(parts g).get p ∧ e.2.1∈(parts g).get p) :
    MixedCode.binaryValue ((parts g).get p).length b M
      (fun v => σ (partVertex g p v))
      (((parts g).get p).idxOf e.1,((parts g).get p).idxOf e.2.1,e.2.2) =
      MixedCode.binaryValue g.vertices b M σ e := by
  have hv := hg.1 e he
  simp only [MixedCode.binaryValue]
  rw [dif_pos ⟨List.idxOf_lt_length_iff.mpr hmem.1,
    List.idxOf_lt_length_iff.mpr hmem.2,hv.2.2⟩,dif_pos hv]
  rw [partVertex_idxOf g p e.1 hmem.1 hv.1,
    partVertex_idxOf g p e.2.1 hmem.2 hv.2.1]

theorem extracted_unaryValue {C R : Type} [One R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (p : PartIndex g)
    (σ : Fin g.vertices → C) (U : Fin u → C → R)
    (e : ℕ × ℕ) (he : e∈g.unaries) (hmem : e.1∈(parts g).get p) :
    MixedCode.unaryValue ((parts g).get p).length u U
      (fun v => σ (partVertex g p v)) (((parts g).get p).idxOf e.1,e.2) =
      MixedCode.unaryValue g.vertices u U σ e := by
  have hv := hg.2 e he
  simp only [MixedCode.unaryValue]
  rw [dif_pos ⟨List.idxOf_lt_length_iff.mpr hmem,hv.2⟩,dif_pos hv]
  rw [partVertex_idxOf g p e.1 hmem hv.1]

theorem extract_binary_prod {C R : Type} [Monoid R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (p : PartIndex g)
    (σ : Fin g.vertices → C) (M : Fin b → Matrix C C R) :
    ((extract g ((parts g).get p)).edges.map
      (MixedCode.binaryValue ((parts g).get p).length b M (fun v => σ (partVertex g p v)))).prod =
      ((g.edges.filter (edgeInside ((parts g).get p))).map
        (MixedCode.binaryValue g.vertices b M σ)).prod := by
  simp only [extract,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  obtain ⟨he,hm⟩ := List.mem_filter.mp he
  exact extracted_binaryValue g hg p σ M e he (by simpa [edgeInside] using hm)

theorem extract_unary_prod {C R : Type} [Monoid R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (p : PartIndex g)
    (σ : Fin g.vertices → C) (U : Fin u → C → R) :
    ((extract g ((parts g).get p)).unaries.map
      (MixedCode.unaryValue ((parts g).get p).length u U (fun v => σ (partVertex g p v)))).prod =
      ((g.unaries.filter (fun e => decide (e.1∈(parts g).get p))).map
        (MixedCode.unaryValue g.vertices u U σ)).prod := by
  simp only [extract,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  obtain ⟨he,hm⟩ := List.mem_filter.mp he
  exact extracted_unaryValue g hg p σ U e he (by simpa using hm)

def assignmentWeight {C R : Type} [CommMonoid R] {b u : ℕ}
    (g : MixedCode) (M : Fin b → Matrix C C R) (U : Fin u → C → R)
    (w : C → R) (σ : Fin g.vertices → C) : R :=
  (∏ v, w (σ v)) * (g.edges.map (MixedCode.binaryValue g.vertices b M σ)).prod *
    (g.unaries.map (MixedCode.unaryValue g.vertices u U σ)).prod

/-- The exact contribution of every global assignment factors over the actual
extracted codes, without positivity or nonvanishing hypotheses. -/
theorem assignmentWeight_factorization {C R : Type} [CommMonoid R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (M : Fin b → Matrix C C R)
    (U : Fin u → C → R) (w : C → R) (σ : Fin g.vertices → C) :
    (∏ p : PartIndex g,
      assignmentWeight (extract g ((parts g).get p)) M U w
        (componentColoringEquiv g C σ p)) = assignmentWeight g M U w σ := by
  have hB := prod_filtered_partition g.edges
    (fun p : PartIndex g => fun e => e.1∈(parts g).get p ∧ e.2.1∈(parts g).get p)
    (MixedCode.binaryValue g.vertices b M σ) (edge_unique_part g hg)
  have hU := prod_filtered_partition g.unaries
    (fun p : PartIndex g => fun e => e.1∈(parts g).get p)
    (MixedCode.unaryValue g.vertices u U σ)
    (fun e he => vertex_unique_part g e.1 (hg.2 e he).1)
  simp only [assignmentWeight,componentColoringEquiv,Equiv.coe_fn_mk,extract_vertices]
  simp_rw [extract_binary_prod g hg,extract_unary_prod g hg]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,background_factorization]
  have hB' : (∏ p : PartIndex g,
      ((g.edges.filter (edgeInside ((parts g).get p))).map
        (MixedCode.binaryValue g.vertices b M σ)).prod) =
      (g.edges.map (MixedCode.binaryValue g.vertices b M σ)).prod := by
    exact hB
  exact congrArg₂ (· * ·) (congrArg (fun x => (∏ v, w (σ v)) * x) hB') (by simpa using hU)

/-- Exact evaluation factorization for the list returned by `components`.
It includes empty inputs, isolated vertices, loops, repeated binary/unary
occurrences, arbitrary backgrounds, and cancellation in any commutative semiring. -/
theorem evaluate_components {C R : Type} [Fintype C] [CommSemiring R] {b u : ℕ}
    (g : MixedCode) (hg : g.Valid b u) (M : Fin b → Matrix C C R)
    (U : Fin u → C → R) (w : C → R) :
    g.evaluate hg M U w = ((components g).map (MixedCode.totalEvaluation M U w)).prod := by
  let F (p : PartIndex g) (τ : PartVertex g p → C) : R :=
    assignmentWeight (extract g ((parts g).get p)) M U w τ
  calc
    g.evaluate hg M U w =
        ∑ σ : Fin g.vertices → C, ∏ p : PartIndex g, F p (componentColoringEquiv g C σ p) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (assignmentWeight_factorization g hg M U w σ).symm
    _ = ∑ τ : (∀ p : PartIndex g, PartVertex g p → C), ∏ p, F p (τ p) :=
      Fintype.sum_equiv (componentColoringEquiv g C) _ _ (fun _ => rfl)
    _ = ∏ p : PartIndex g, ∑ τ : PartVertex g p → C, F p τ :=
      (Fintype.prod_sum F).symm
    _ = ∏ p : PartIndex g,
        MixedCode.totalEvaluation M U w (extract g ((parts g).get p)) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [MixedCode.totalEvaluation_valid _ _ _ _ (extract_valid g hg _)]
      rfl
    _ = ((components g).map (MixedCode.totalEvaluation M U w)).prod := by
      simpa only [components,List.map_map,Function.comp_def,List.get_eq_getElem] using
        Fin.prod_univ_fun_getElem (parts g)
          (fun xs => MixedCode.totalEvaluation M U w (extract g xs))

end PlanarHom.GraphComponentCode
