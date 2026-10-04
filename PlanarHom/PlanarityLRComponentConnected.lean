import PlanarHom.PlanarityLRComponentGraph
import PlanarHom.PottsRandomCluster

/-! NEW genuine connectedness of every literal DFS-root component graph. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

 theorem componentDartHost_val (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (a : Dart (ComponentEdge g r)) :
    ((componentGraph g hg r).dartPair a).1.val.val=dartHost g (componentDartLift g r a) := by
  rw [componentDartLift_host]
  exact (eraseDart_host g hg _).symm

 theorem dartPair_connected {V E : Type*} [Fintype E] (G : MultiGraph V E) (a : Dart E) :
    G.componentSetoid Finset.univ (G.dartPair a).1 (G.dartPair (reversePerm E a)).1 := by
  rcases a with ⟨e,b⟩
  have hh : G.componentSetoid Finset.univ (G.src e) (G.dst e) :=
    Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
  cases b
  · exact hh.symm
  · exact hh

 theorem componentGraph_connected (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) :
    ∀u v : ComponentVertex g r.val, (componentGraph g hg r.val).componentSetoid Finset.univ u v := by
  let root : ComponentVertex g r.val := ⟨r,componentRoot_eq_self g r.isLt hr⟩
  have hall : ∀ n, ∀v : ComponentVertex g r.val, height g v.val.val=n →
      (componentGraph g hg r.val).componentSetoid Finset.univ root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hn
        by_cases hz : height g v.val.val=0
        · have hv : v=root := Subtype.ext (Fin.ext ((componentRoot_eq_self g v.val.isLt hz).symm.trans v.property))
          rw [hv]
        · have hpos := Nat.pos_of_ne_zero hz
          have hp := parentEdge_tree g hg v.val.isLt hpos
          let e : Fin g.edges.length := ⟨parentEdge g v.val.val,parentEdge_lt g v.val.isLt hpos⟩
          have heroot : componentRoot g (source g e.val)=r.val := by
            rw [hp.2.2]
            exact (componentRoot_eq_of_desc g v.val.isLt
              (Or.inr (parentVertex_ancestor g v.val.isLt hpos))).trans v.property
          let ce : ComponentEdge g r.val := ⟨e,heroot⟩
          let a : Dart (ComponentEdge g r.val) := (ce,(typedOutward g e).2)
          have halift : componentDartLift g r.val a=typedOutward g e := rfl
          let p := ((componentGraph g hg r.val).dartPair a).1
          have hparent : p.val.val=parentVertex g v.val.val := by
            rw [componentDartHost_val g hg r.val a,halift,dartHost_typedOutward]
            exact hp.2.2
          have htarget : ((componentGraph g hg r.val).dartPair (reversePerm _ a)).1=v := by
            apply Subtype.ext
            apply Fin.ext
            rw [componentDartHost_val,componentDartLift_reverse,halift,dartHost_reverse_typedOutward]
            exact hp.2.1
          have hlt : height g p.val.val<n := by
            rw [hparent,←hn]
            exact parentVertex_height_lt g v.val.isLt hpos
          have hprev := ih _ hlt p rfl
          exact Relation.EqvGen.trans root p v hprev
            (by simpa only [htarget] using dartPair_connected (componentGraph g hg r.val) a)
  intro u v
  exact Relation.EqvGen.trans u root v (Relation.EqvGen.symm root u (hall _ u rfl)) (hall _ v rfl)

end PlanarHom.PlanarityLRRealization
