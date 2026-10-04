import PlanarHom.PlanarityRowFacePermutation
import PlanarHom.PlanarityLRDualReachability

/-! NEW arbitrary-row dual reachability, transported through actual DFS
connectivity and the literal cyclic host rows. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization
theorem label_reachable_sameHost {F : Type*} (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (T : RotationRows (g.toMultiGraph hg)) (label : Dart (Fin g.edges.length) → F) (R : F → F → Prop)
    (hface : ∀ a, label (T.facePerm a) = label a)
    (hreverse : ∀ a, R (label a) (label (reversePerm _ a)))
    (a b : Dart (Fin g.edges.length)) (hab : dartHost g a = dartHost g b) :
    Relation.ReflTransGen R (label a) (label b) := by
  let rows := T
  have hhost : ((g.toMultiGraph hg).dartPair a).1 = ((g.toMultiGraph hg).dartPair b).1 := by
    apply Fin.ext
    simpa only [dartHost,eraseDart_host g hg] using hab
  obtain ⟨n,hn⟩ := rows.exists_rotation_iterate_of_sameHost a b hhost
  have hstep (x : Dart (Fin g.edges.length)) : R (label x) (label (rows.rotation x)) := by
    have he : label (rows.rotation x) = label (reversePerm _ x) := by
      simpa only [RotationRows.facePerm,Equiv.trans_apply,reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta,rows] using
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
    (T : RotationRows (g.toMultiGraph hg)) (label : Dart (Fin g.edges.length) → F) (R : F → F → Prop)
    (hface : ∀ a, label (T.facePerm a) = label a)
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
      · exact label_reachable_sameHost g hg T label R hface hreverse x y hh

end PlanarHom.PlanarityRowFaceCode
