import PlanarHom.FisherCubicRotation
import PlanarHom.FisherExpansionConnected

/-! NEW connectivity of literal polygon/triangle replacement and transport
through endpoint-preserving dart relabeling. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E W F : Type*} [Fintype E] [Fintype F]
variable {G : MultiGraph V E} {H : MultiGraph W F}

 theorem dart_hosts_connected (G : MultiGraph V E) (a : Dart E) :
    G.componentSetoid Finset.univ (G.dartPair a).1 (G.dartPair (reversePerm E a)).1 := by
  rcases a with ⟨e,b⟩
  have h : G.componentSetoid Finset.univ (G.src e) (G.dst e) :=
    Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
  cases b
  · exact h.symm
  · exact h

 theorem DartRelabel.connected (e : DartRelabel G H)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) :
    ∀u v,H.componentSetoid Finset.univ u v := by
  let color : V→H.Components Finset.univ := fun v=>Quotient.mk _ (e.vertex v)
  have hc : G.EdgeConstant Finset.univ color := by
    intro edge _
    have h := H.dart_hosts_connected (e.dart (edge,true))
    rw [←e.reverse,e.host,e.host] at h
    exact Quotient.sound h
  intro u v
  have h := G.edgeConstant_respects Finset.univ color hc (hG (e.vertex.symm u) (e.vertex.symm v))
  exact Quotient.exact (by simpa only [color,e.vertex.apply_symm_apply] using h)

end PlanarHom.MultiGraph

namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)] {G : MultiGraph V E}
variable (R : RotationRows G)

 theorem polygon_same_host_connected (a b : Dart E) (hh : (G.dartPair a).1=(G.dartPair b).1) :
    (polygonGraph R).componentSetoid Finset.univ a b := by
  obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b hh
  have hi : ∀n,(polygonGraph R).componentSetoid Finset.univ a (R.rotation^[n] a) := by
    intro n
    induction n with
    | zero => exact .refl _
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact Relation.EqvGen.trans _ _ _ ih
          (Relation.EqvGen.rel _ _ ⟨.inr (R.rotation^[n] a),Finset.mem_univ _,rfl,rfl⟩)
  exact hn ▸ hi n

 theorem polygon_connected (hinc : ∀v,∃a : Dart E,(G.dartPair a).1=v)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) :
    ∀a b : Dart E,(polygonGraph R).componentSetoid Finset.univ a b := by
  let anchor : V→Dart E := fun v=>Classical.choose (hinc v)
  have ha : ∀v,(G.dartPair (anchor v)).1=v := fun v=>Classical.choose_spec (hinc v)
  let color : V→(polygonGraph R).Components Finset.univ := fun v=>Quotient.mk _ (anchor v)
  have hc : G.EdgeConstant Finset.univ color := by
    intro e _
    have hs := polygon_same_host_connected R (anchor (G.src e)) (e,true) (ha _)
    have ht := polygon_same_host_connected R (e,false) (anchor (G.dst e)) (ha _).symm
    have he : (polygonGraph R).componentSetoid Finset.univ (e,true) (e,false) :=
      Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩
    exact Quotient.sound (Relation.EqvGen.trans _ _ _ hs (Relation.EqvGen.trans _ _ _ he ht))
  intro a b
  have hab : (polygonGraph R).componentSetoid Finset.univ
      (anchor (G.dartPair a).1) (anchor (G.dartPair b).1) :=
    Quotient.exact (G.edgeConstant_respects Finset.univ color hc (hG _ _))
  exact Relation.EqvGen.trans _ _ _ (polygon_same_host_connected R a _ (ha _).symm)
    (Relation.EqvGen.trans _ _ _ hab (polygon_same_host_connected R _ b (ha _)))

 theorem cubicInherited_connected (p : (V×Fin 3)≃(E×Bool))
    (R : RotationRows (cubicOriginal p))
    (hG : ∀u v,(cubicOriginal p).componentSetoid Finset.univ u v) :
    ∀u v,(cubicDecoration p).componentSetoid Finset.univ u v :=
  (cubicRelabel p R).connected (polygon_connected R (cubicOriginal_incident p) hG)

end PlanarHom.Fisher
