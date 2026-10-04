import PlanarHom.PlanarityLRComponents
import Mathlib.Data.Finset.Card

/-! NEW bottom-up induction on the actual computed DFS children. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem height_lt_vertices (g : MixedCode) {v : ℕ} (hv : v < g.vertices) : height g v < g.vertices := by
  have hn : (v::ancestors g v).Nodup := List.nodup_cons.mpr
    ⟨fun h => (lt_irrefl _ (ancestors_height_lt g hv h)),ancestors_nodup g hv⟩
  have hsub : (v::ancestors g v).toFinset ⊆ Finset.range g.vertices := by
    intro u hu
    rw [List.mem_toFinset,List.mem_cons] at hu
    rw [Finset.mem_range]
    rcases hu with rfl | hu
    · exact hv
    · exact ancestors_valid g hv hu
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn,Finset.card_range,List.length_cons] at hcard
  change height g v+1≤g.vertices at hcard
  omega

 theorem child_depth_remainder_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e=true) :
    g.vertices-height g (target g e) < g.vertices-height g (source g e) := by
  have ht := (source_target_valid g hg (of_decide_eq_true he).1).2
  have hb := height_lt_vertices g ht
  have hs := tree_height_succ g hg he
  omega

/-- A property may be constructed at each vertex after its actual tree children,
with termination derived from finite valid vertex labels and exact DFS heights. -/
theorem computed_children_induction (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (P : ℕ → Prop)
    (hstep : ∀ v, v < g.vertices →
      (∀ e, isTree g e=true → source g e=v → P (target g e)) → P v) :
    ∀ v, v < g.vertices → P v := by
  suffices ∀ k v, v < g.vertices → g.vertices-height g v=k → P v by
    intro v hv
    exact this _ v hv rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v hv hk
      apply hstep v hv
      intro e he hsource
      have ht := (source_target_valid g hg (of_decide_eq_true he).1).2
      apply ih (g.vertices-height g (target g e)) ?_ (target g e) ht rfl
      rw [← hk,← hsource]
      exact child_depth_remainder_lt g hg he

end PlanarHom.PlanarityLRDirect
