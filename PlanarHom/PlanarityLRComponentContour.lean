import PlanarHom.PlanarityLRComponentRows
import PlanarHom.PlanarityLRComponentPortHeights
import PlanarHom.PlanarityLRForestFaceCount

/-! NEW exact component contour restriction and its original computed port word. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

 def componentSelected (g : MixedCode) (r : ℕ) (e : ComponentEdge g r) : Bool := isTree g e.val.val

 def componentContour (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) : Equiv.Perm (Dart (ComponentEdge g r)) :=
  contourPermutation (componentRows g hg r rows) (componentSelected g r)

 theorem componentContour_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) :
    componentDartLift g r (componentContour g hg r rows a)=
      dfsContourForRows g hg rows (componentDartLift g r a) := by
  by_cases ha : isTree g a.1.val.val=true
  · rw [componentContour,contourPermutation_selected _ _ a ha,
      componentRows_rotation_lift,componentDartLift_reverse,dfsContourForRows,
      contourPermutation_selected _ _ _ ha]
  · have hf := Bool.eq_false_iff.mpr ha
    rw [componentContour,contourPermutation_port _ _ a hf,componentRows_rotation_lift,
      dfsContourForRows,contourPermutation_port _ _ _ hf]

 theorem componentContour_iterate_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) (n : ℕ) :
    componentDartLift g r ((componentContour g hg r rows)^[n] a)=
      (dfsContourForRows g hg rows)^[n] (componentDartLift g r a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',componentContour_lift,ih,Function.iterate_succ_apply']

 theorem componentContour_singleCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a b : Dart (ComponentEdge g r)) :
    (componentContour g hg r rows).SameCycle a b := by
  have hroot : componentRoot g (dartHost g (componentDartLift g r a))=
      componentRoot g (dartHost g (componentDartLift g r b)) :=
    (componentDartEquiv g hg r a).property.trans (componentDartEquiv g hg r b).property.symm
  obtain ⟨n,hn⟩ := (dfsContourForRows_sameCycle_of_componentRoot_eq g hg rows _ _ hroot).exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  apply componentDartLift_injective g r
  rw [zpow_natCast,←Equiv.Perm.iterate_eq_pow,componentContour_iterate_lift,Equiv.Perm.iterate_eq_pow,hn]

 theorem componentContour_period (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) :
    Function.minimalPeriod (componentContour g hg r rows) a=
      Function.minimalPeriod (dfsContourForRows g hg rows) (componentDartLift g r a) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change _=a ↔ _=componentDartLift g r a
  rw [←componentContour_iterate_lift]
  exact (componentDartLift_injective g r).eq_iff.symm

 theorem componentContour_word_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) :
    (orbitPrefix (componentContour g hg r rows) (Function.minimalPeriod (componentContour g hg r rows) a) a).map
      (componentDartLift g r)=
      orbitPrefix (dfsContourForRows g hg rows)
        (Function.minimalPeriod (dfsContourForRows g hg rows) (componentDartLift g r a))
        (componentDartLift g r a) := by
  simp only [orbitPrefix,List.map_map,Function.comp_def,componentContour_iterate_lift,componentContour_period]

 theorem componentContour_ports_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (ComponentEdge g r)) :
    (contourPortWord (componentRows g hg r rows) (componentSelected g r) a).map (componentDartLift g r)=
      contourPortWord rows (fun e => isTree g e.val) (componentDartLift g r a) := by
  have h := congrArg (List.filter (fun a : Dart (Fin g.edges.length) => !(isTree g a.1.val)))
    (componentContour_word_lift g hg r rows a)
  simpa only [List.filter_map,Function.comp_def,orbitPrefix,contourPortWord,componentContour,
    dfsContourForRows,componentSelected,componentDartLift] using h

 def computedComponentStart (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) (r : ℕ)
    (base : Dart (ComponentEdge g r)) : Dart (ComponentEdge g r) :=
  (componentDartEquiv g hg r).symm
    ⟨componentContourStart g hg bits (componentDartLift g r base),
      (componentStart_componentRoot g hg bits _).trans (componentDartEquiv g hg r base).property⟩

@[simp] theorem computedComponentStart_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base : Dart (ComponentEdge g r)) :
    componentDartLift g r (computedComponentStart g hg bits r base)=
      componentContourStart g hg bits (componentDartLift g r base) := rfl

 theorem componentVisibleWord_lift (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base : Dart (ComponentEdge g r)) :
    (visibleContourWord (componentRows g hg r (directRotationRows g hg bits)).rotation (componentSelected g r)
        (computedComponentStart g hg bits r base)).map (fun a => (a.1.val.val,a.2))=
      componentPortWord g hg bits (componentDartLift g r base) := by
  have h := congrArg (List.map (componentDartLift g r))
    (visibleContourWord_erase (componentRows g hg r (directRotationRows g hg bits)) (componentSelected g r)
      (computedComponentStart g hg bits r base))
  rw [componentContour_ports_lift,computedComponentStart_lift] at h
  simpa only [List.map_map,Function.comp_def,componentDartLift,componentPortWord] using h

end PlanarHom.PlanarityLRRealization
