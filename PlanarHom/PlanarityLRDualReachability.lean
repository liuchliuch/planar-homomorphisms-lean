import PlanarHom.PlanarityLRDartConnectivity

/-! NEW dual reachability: actual row cycles and occurrence reversal connect
all computed faces in a DFS component. No planar embedding is used or assumed. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect

namespace RotationRows
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]

theorem rotation_iterate_host (R : RotationRows G) (a : Dart E) (n : ℕ) :
    (G.dartPair (R.rotation^[n] a)).1 = (G.dartPair a).1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',R.rotation_host,ih]

theorem rotation_iterate_eq_formPerm (R : RotationRows G) (a : Dart E) (n : ℕ) :
    R.rotation^[n] a = ((R.row (G.dartPair a).1).formPerm)^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',R.rotation_apply,R.rotation_iterate_host,ih,Function.iterate_succ_apply']

theorem exists_rotation_iterate_of_sameHost [Finite (Dart E)] (R : RotationRows G)
    (a b : Dart E) (hab : (G.dartPair a).1 = (G.dartPair b).1) : ∃ n, R.rotation^[n] a=b := by
  have ha := (R.mem (G.dartPair a).1 a).mpr rfl
  have hb := (R.mem (G.dartPair a).1 b).mpr hab.symm
  have hc := (R.nodup (G.dartPair a).1).isCycleOn_formPerm.2 ha hb
  obtain ⟨n,hn⟩ := hc.exists_nat_pow_eq
  exact ⟨n,by rw [R.rotation_iterate_eq_formPerm,Equiv.Perm.iterate_eq_pow]; exact hn⟩
end RotationRows

theorem label_reachable_sameHost {F : Type*} (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (label : Dart (Fin g.edges.length) → F) (R : F → F → Prop)
    (hface : ∀ a, label (facePermutation g hg bits a) = label a)
    (hreverse : ∀ a, R (label a) (label (reversePerm _ a)))
    (a b : Dart (Fin g.edges.length)) (hab : dartHost g a = dartHost g b) :
    Relation.ReflTransGen R (label a) (label b) := by
  let rows := directRotationRows g hg bits
  have hhost : ((g.toMultiGraph hg).dartPair a).1 = ((g.toMultiGraph hg).dartPair b).1 := by
    apply Fin.ext
    simpa only [dartHost,eraseDart_host g hg] using hab
  obtain ⟨n,hn⟩ := rows.exists_rotation_iterate_of_sameHost a b hhost
  have hstep (x : Dart (Fin g.edges.length)) : R (label x) (label (rows.rotation x)) := by
    have he : label (rows.rotation x) = label (reversePerm _ x) := by
      simpa only [facePermutation,Equiv.trans_apply,reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta,rows] using
        hface (reversePerm _ x)
    rw [he]
    exact hreverse x
  suffices ∀ n, Relation.ReflTransGen R (label a) (label (rows.rotation^[n] a)) by
    simpa only [hn] using this n
  intro n
  induction n with
  | zero => exact .refl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail (hstep _)

/-- General label transport interface. Actual dual labels instantiate its two
local identities, so this never assumes dual connectivity as input. -/
theorem dualReachable_of_componentRoot_eq {F : Type*} (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (label : Dart (Fin g.edges.length) → F) (R : F → F → Prop)
    (hface : ∀ a, label (facePermutation g hg bits a) = label a)
    (hreverse : ∀ a, R (label a) (label (reversePerm _ a)))
    (a b : Dart (Fin g.edges.length))
    (hroot : componentRoot g (dartHost g a) = componentRoot g (dartHost g b)) :
    Relation.ReflTransGen R (label a) (label b) := by
  have hpath := dartConnected_of_componentRoot_eq g hg a b hroot
  clear hroot
  induction hpath with
  | refl => exact .refl
  | @tail x y hxy hstep ih =>
      apply ih.trans
      rcases hstep with rfl | hh
      · exact .single (hreverse x)
      · exact label_reachable_sameHost g hg bits label R hface hreverse x y hh

end PlanarHom.PlanarityLRRealization
