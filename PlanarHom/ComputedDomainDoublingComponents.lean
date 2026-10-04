import PlanarHom.ComputedDomainDoublingSemantics

/-! NEW inherited proper sides for the literal component-extraction program. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ComputedDomainDoubling
open Complexity Complexity.MixedCode GraphComponentCode BipartiteRankTwoTractability

 def HasProperSides (g : MixedCode) (hg : g.Valid 1 0) : Prop :=
  ∃δ : Fin g.vertices→Bool,∀e,δ ((g.toMultiGraph hg).src e)≠δ ((g.toMultiGraph hg).dst e)

theorem coloring_iff_proper (g : MixedCode) (hg : g.Valid 1 0) :
    (coloring g).1=true ↔ HasProperSides g hg := by
  constructor
  · intro h
    refine ⟨fun v=>PlanarityParitySolver.lookup (coloring g).2 v.val,?_⟩
    intro e
    exact coloring_sound g h (g.edges.get e) (List.get_mem _ _)
  · rintro ⟨δ,hδ⟩
    apply (coloring_complete g).mpr
    refine ⟨fun v=>if h:v<g.vertices then δ ⟨v,h⟩ else false,?_⟩
    intro e he
    obtain ⟨n,hn⟩:=List.get_of_mem he
    have h:=hδ n
    have hv:=hg.1 e he
    have hs : (g.toMultiGraph hg).src n=⟨e.1,hv.1⟩ := by
      apply Fin.ext
      exact congrArg Prod.fst hn
    have ht : (g.toMultiGraph hg).dst n=⟨e.2.1,hv.2.1⟩ := by
      apply Fin.ext
      exact congrArg (fun a : ℕ×ℕ×ℕ=>a.2.1) hn
    rw [hs,ht] at h
    simpa only [dif_pos hv.1,dif_pos hv.2.1] using h

def BipartitePlanarCode (g : MixedCode) : Prop := g.PlanarValid 1 0 ∧ (coloring g).1=true

theorem component_hasProperSides (g : MixedCode) (hg : g.Valid 1 0)
    (hp : HasProperSides g hg) (query : MixedCode) (hq : query∈components g) :
    HasProperSides query (components_valid g hg query hq) := by
  obtain ⟨δ,hδ⟩:=hp
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hq
  let emb:=extractIncidenceEmbedding g hg xs (part_nodup g xs hxs) (part_vertex_lt g xs hxs)
  refine ⟨fun v=>δ (emb.vertex v),?_⟩
  intro e
  dsimp only
  rw [←emb.src_eq,←emb.dst_eq]
  exact hδ (emb.edge e)

theorem component_coloring (g : MixedCode) (hg : g.Valid 1 0)
    (hp : (coloring g).1=true) (query : MixedCode) (hq : query∈components g) :
    (coloring query).1=true :=
  (coloring_iff_proper query (components_valid g hg query hq)).mpr
    (component_hasProperSides g hg ((coloring_iff_proper g hg).mp hp) query hq)

variable {C K : Type} [Fintype C] [Field K]

theorem components_value (g : MixedCode) (hg : g.Valid 1 0) (hp : (coloring g).1=true)
    (M : Matrix C C K) (w : C→K) :
    g.evaluate hg (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w)=
      2^(components g).length*g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  rw [evaluate_components g hg (fun _=>matrix M) (fun u=>u.elim0) (weights w),
    evaluate_components g hg (fun _=>M) (fun u=>u.elim0) w]
  have he : (components g).map (totalEvaluation (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w))=
      (components g).map (fun c=>2*totalEvaluation (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w c) := by
    apply List.map_congr_left
    intro c hc
    have hv:=components_valid g hg c hc
    rw [totalEvaluation_valid _ _ _ _ hv,totalEvaluation_valid _ _ _ _ hv]
    exact connected_value c hv (components_connected g hg c hc) (components_nonempty g c hc)
      (component_coloring g hg hp c hc) M w
  rw [he,List.prod_map_mul]
  simp

end PlanarHom.ComputedDomainDoubling
