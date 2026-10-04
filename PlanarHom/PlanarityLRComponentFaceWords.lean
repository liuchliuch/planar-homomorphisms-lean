import PlanarHom.PlanarityLRComponentRows
import PlanarHom.PlanarityFaceOrientationCorrectness
import PlanarHom.FinitePermutationCycleWords
import PlanarHom.OccurrenceKasteleynBoundarySigns

/-! NEW exact list/fiber semantics for the actual component face cycles. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityFaceCode FinitePermutationCycles FinitePermutationReturnWords

 theorem componentFace_iterate_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) (n : ℕ) :
    componentDartLift g r ((componentFace g hg r rows)^[n] a)=
      (rows.rotation * reversePerm (Fin g.edges.length))^[n] (componentDartLift g r a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',componentFace_lift,ih,Function.iterate_succ_apply']

 theorem componentFace_sameCycle_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (ComponentEdge g r)) :
    (componentFace g hg r rows).SameCycle a b ↔
      (rows.rotation * reversePerm (Fin g.edges.length)).SameCycle (componentDartLift g r a) (componentDartLift g r b) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    rw [zpow_natCast,←Equiv.Perm.iterate_eq_pow,←componentFace_iterate_lift,Equiv.Perm.iterate_eq_pow,hn]
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    apply componentDartLift_injective g r
    rw [zpow_natCast,←Equiv.Perm.iterate_eq_pow,componentFace_iterate_lift,Equiv.Perm.iterate_eq_pow,hn]

 theorem componentFace_period (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) :
    Function.minimalPeriod (componentFace g hg r rows) a=
      Function.minimalPeriod (rows.rotation * reversePerm (Fin g.edges.length)) (componentDartLift g r a) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change _=a ↔ _=componentDartLift g r a
  rw [←componentFace_iterate_lift]
  exact (componentDartLift_injective g r).eq_iff.symm

 theorem componentFaceWord_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) (r : ℕ)
    (a : Dart (ComponentEdge g r)) :
    (cycleWord (componentFace g hg r (directRotationRows g hg bits)) a).map
      (fun b => eraseDart (componentDartLift g r b))=
      boundary g bits (eraseDart (componentDartLift g r a)) := by
  rw [boundary_eq_period_walk g hg bits]
  simp only [cycleWord,orbitPrefix,List.map_map,Function.comp_def,componentFace_iterate_lift,componentFace_period]
  rfl

 theorem boundary_perm_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a b : Dart (Fin g.edges.length)) (h : (facePermutation g hg bits).SameCycle a b) :
    (boundary g bits (eraseDart a)).Perm (boundary g bits (eraseDart b)) := by
  rw [boundary_eq_period_walk g hg bits a,boundary_eq_period_walk g hg bits b]
  simpa only [cycleWord,orbitPrefix,List.map_map,Function.comp_def] using
    (cycleWord_perm_of_sameCycle (facePermutation g hg bits) a b h).map eraseDart

 theorem boundaryById_perm_componentFaceWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (a : Dart (ComponentEdge g r)) :
    (boundaryById g bits (faceId g bits (eraseDart (componentDartLift g r a)))).Perm
      ((cycleWord (componentFace g hg r (directRotationRows g hg bits)) a).map
        (fun b => eraseDart (componentDartLift g r b))) := by
  let raw := componentDartLift g r a
  let rep := liftDart (representative g bits (eraseDart raw)) (representative_valid g hg bits raw)
  have hc : (facePermutation g hg bits).SameCycle raw rep := by
    apply (mem_orbit_iff_sameCycle g hg bits raw rep).mp
    simpa only [rep,erase_liftDart] using representative_mem_orbit g hg bits raw
  rw [componentFaceWord_raw,boundaryById_faceId g hg bits raw.1.isLt]
  simpa only [rep,erase_liftDart] using boundary_perm_sameCycle g hg bits rep raw hc.symm

end PlanarHom.PlanarityLRRealization
