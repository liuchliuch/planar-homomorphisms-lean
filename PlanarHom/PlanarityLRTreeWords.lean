import PlanarHom.PlanarityLRWordPaths

/-! NEW injectivity and exact ancestry-prefix semantics of ranked tree words. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem treeWord_injective (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {u v : ℕ} (hu : u<g.vertices) (hv : v<g.vertices)
    (hr : componentRoot g u=componentRoot g v) (he : treeWord g bits u=treeWord g bits v) : u=v := by
  induction h : height g u using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    have hd : height g u=height g v := by simpa only [treeWord_length] using congrArg List.length he
    by_cases hz : n=0
    · have huz:height g u=0 := h.trans hz
      have hvz:height g v=0 := hd.symm.trans huz
      simpa only [componentRoot_eq_self g hu huz,componentRoot_eq_self g hv hvz] using hr
    · have hpu:0<height g u := by omega
      have hpv:0<height g v := by omega
      have hdu:=parent_height g hu hpu
      have hdv:=parent_height g hv hpv
      have hau:=parentVertex_ancestor g hu hpu
      have hav:=parentVertex_ancestor g hv hpv
      have hup:=ancestors_valid g hu hau
      have hvp:=ancestors_valid g hv hav
      have hrp : componentRoot g (parentVertex g u)=componentRoot g (parentVertex g v) :=
        (componentRoot_eq_of_desc g hu (Or.inr hau)).trans
          (hr.trans (componentRoot_eq_of_desc g hv (Or.inr hav)).symm)
      rw [treeWord_parent g bits hu hpu,treeWord_parent g bits hv hpv] at he
      have hs := List.concat_inj.mp (show List.concat (treeWord g bits (parentVertex g u))
          ((orderedOutgoing g bits (parentVertex g u)).idxOf (parentEdge g u)) =
          List.concat (treeWord g bits (parentVertex g v))
          ((orderedOutgoing g bits (parentVertex g v)).idxOf (parentEdge g v)) by
        simpa only [List.concat_eq_append] using he)
      have hparents : parentVertex g u=parentVertex g v :=
        ih (height g (parentVertex g u)) (by omega) hup hvp hrp hs.1 rfl
      apply parentEdge_injective g hu hv hpu hpv
      have hmu : parentEdge g u∈orderedOutgoing g bits (parentVertex g v) := by
        simpa only [hparents] using parentEdge_mem_orderedOutgoing g hg bits hu hpu
      exact (List.idxOf_inj hmu (parentEdge_mem_orderedOutgoing g hg bits hv hpv)).mp
        (by simpa only [hparents] using hs.2)

 theorem treeWord_prefix_iff_desc (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {u v : ℕ} (hu : u<g.vertices) (hv : v<g.vertices)
    (hr : componentRoot g u=componentRoot g v) :
    (treeWord g bits u).IsPrefix (treeWord g bits v) ↔ Desc g u v := by
  refine ⟨?_,treeWord_prefix_of_desc g bits hv⟩
  intro hp
  induction h : height g v using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    have hle : height g u≤height g v := by simpa only [treeWord_length] using hp.length_le
    by_cases he:height g u=height g v
    · have hw:=hp.eq_of_length (by simp only [treeWord_length,he])
      exact Or.inl (treeWord_injective g hg bits hu hv hr hw)
    · have hpos : 0<height g v := by omega
      have hav:=parentVertex_ancestor g hv hpos
      have hvp:=ancestors_valid g hv hav
      have hdv:=parent_height g hv hpos
      have hpp:=(treeWord_prefix_of_desc g bits hv (Or.inr hav))
      have hshort : (treeWord g bits u).length≤(treeWord g bits (parentVertex g v)).length := by
        simp only [treeWord_length]; omega
      have hp' := List.prefix_of_prefix_length_le hp hpp hshort
      have hrp : componentRoot g u=componentRoot g (parentVertex g v) :=
        hr.trans (componentRoot_eq_of_desc g hv (Or.inr hav)).symm
      have hd:=ih (height g (parentVertex g v)) (by omega) hu hvp hrp hp' rfl
      exact desc_trans g hv hd (Or.inr hav)

end PlanarHom.PlanarityLRDirect
