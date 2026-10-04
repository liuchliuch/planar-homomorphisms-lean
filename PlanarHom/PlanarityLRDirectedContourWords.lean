import PlanarHom.PlanarityLRContourReorientation
import PlanarHom.PlanarityLRSubtreeWordStart

/-! NEW exact row expansion in the DFS-directed graph used by geometric routing. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

def directedExcursionWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
  (hostExcursionWord g hg (dfsPullRows g hg rows) ((dfsDartEquiv g).symm a)).map (dfsDartEquiv g)

theorem directed_contour_word_eq_row_expansion (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) :
    orbitPrefix (contourPermutation rows (fun e => isTree g e.val))
        (Function.minimalPeriod (contourPermutation rows (fun e => isTree g e.val)) a) a =
      ((rows.row ((dfsGraph g hg).dartPair a).1).rotate
        ((rows.row ((dfsGraph g hg).dartPair a).1).idxOf a)).flatMap (directedExcursionWord g hg rows) := by
  let e := dfsDartEquiv g
  let b := e.symm a
  have heb : e b=a := e.apply_symm_apply a
  have hh := congrArg (List.map e) (contour_word_eq_row_expansion g hg (dfsPullRows g hg rows) b)
  rw [dfsDartEquiv_contour_word,heb] at hh
  have hrow : (dfsPullRows g hg rows).row ((g.toMultiGraph hg).dartPair b).1=
      (rows.row ((dfsGraph g hg).dartPair a).1).map e.symm := by
    change (rows.row ((g.toMultiGraph hg).dartPair b).1).map e.symm=_
    rw [←dfsDartEquiv_host g hg b,heb]
  rw [hrow] at hh
  have hidx : ((rows.row ((dfsGraph g hg).dartPair a).1).map e.symm).idxOf b=
      (rows.row ((dfsGraph g hg).dartPair a).1).idxOf a := by
    have h := idxOf_map_embedding e.symm e.symm.injective (rows.row ((dfsGraph g hg).dartPair a).1) a
    simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h
  rw [hidx,←List.map_rotate,List.map_flatMap,List.flatMap_map] at hh
  exact hh

theorem directed_contour_filter_eq_afterParentInputs (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length))
    (keep : Dart (Fin g.edges.length) → Bool)
    (hempty : (directedExcursionWord g hg rows a).filter keep=[]) :
    (orbitPrefix (contourPermutation rows (fun e => isTree g e.val))
        (Function.minimalPeriod (contourPermutation rows (fun e => isTree g e.val)) a) a).filter keep =
      afterParentInputs (rows.row ((dfsGraph g hg).dartPair a).1) a
        (fun b => (directedExcursionWord g hg rows b).filter keep) := by
  rw [directed_contour_word_eq_row_expansion,List.filter_flatMap]
  have h := rotate_flatMap_eq_afterParentInputs (rows.row ((dfsGraph g hg).dartPair a).1) a
    (fun b => (directedExcursionWord g hg rows b).filter keep) ((rows.mem _ _).mpr rfl) hempty
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h

def directedSubtreePorts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) : List (Dart (Fin g.edges.length)) :=
  (subtreeContourPorts g hg (dfsPullRows g hg rows) e).map (dfsDartEquiv g)

def directedSubtreeKeep (g : MixedCode) (e : Fin g.edges.length) (a : Dart (Fin g.edges.length)) : Bool :=
  subtreePortKeep g e ((dfsDartEquiv g).symm a)

theorem directedSubtreeKeep_eq_true (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : Fin g.edges.length) (a : Dart (Fin g.edges.length)) :
    directedSubtreeKeep g e a=true ↔ isTree g a.1.val=false ∧
      Desc g (target g e.val) ((dfsGraph g hg).dartPair a).1.val := by
  have hh := congrArg Fin.val (dfsDartEquiv_host g hg ((dfsDartEquiv g).symm a))
  rw [Equiv.apply_symm_apply,←eraseDart_host g hg] at hh
  change _=dartHost g ((dfsDartEquiv g).symm a) at hh
  rw [dfsDartEquiv_symm] at hh
  rw [directedSubtreeKeep,subtreePortKeep_eq_true,dfsDartEquiv_symm,dfsDartEquiv_index,←hh]

theorem mem_directedSubtreePorts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (a : Dart (Fin g.edges.length)) :
    a∈directedSubtreePorts g hg rows e ↔ directedSubtreeKeep g e a=true := by
  constructor
  · rintro h
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    rw [directedSubtreeKeep,Equiv.symm_apply_apply,subtreePortKeep_eq_true]
    exact (mem_subtreeContourPorts g hg _ e he b).mp hb
  · intro h
    refine List.mem_map.mpr ⟨(dfsDartEquiv g).symm a,?_,Equiv.apply_symm_apply _ _⟩
    exact (mem_subtreeContourPorts g hg _ e he _).mpr ((subtreePortKeep_eq_true g e _).mp h)

theorem directedSubtreePorts_reverse_start (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    directedSubtreePorts g hg rows e=
      (orbitPrefix (contourPermutation rows (fun e => isTree g e.val))
        (Function.minimalPeriod (contourPermutation rows (fun e => isTree g e.val)) (e,false))
        (e,false)).filter (directedSubtreeKeep g e) := by
  have h := congrArg (List.filter (directedSubtreeKeep g e))
    (dfsDartEquiv_contour_word g hg rows (reversePerm _ (typedOutward g e)))
  simp only [List.filter_map,directedSubtreeKeep,Function.comp_def,Equiv.symm_apply_apply,
    dfsDartEquiv_reverse,dfsDartEquiv_outward] at h
  change ((orbitPrefix _ _ _).filter (subtreePortKeep g e)).map (dfsDartEquiv g)=_ at h
  rw [←subtreeContourPorts_reverse_start g hg (dfsPullRows g hg rows) e he] at h
  exact h

end PlanarHom.PlanarityLRRealization
