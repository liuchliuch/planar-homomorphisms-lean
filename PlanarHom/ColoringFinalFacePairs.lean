import PlanarHom.ColoringFramedSpliceProgram
import PlanarHom.DisjointFaceSpliceApplication

/-! The canonical source face program is exactly the literal finite sequence
of its producer/consumer marker swaps. This unfolds both nested loop levels. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D]

 theorem applyPairSplices_append (P : Equiv.Perm D) (ps qs : List (D×D)) :
    applyPairSplices P (ps++qs)=applyPairSplices (applyPairSplices P ps) qs := List.foldl_append

 theorem splicePrefix_eq_applyPairSplices (P : Equiv.Perm D) (x y : ℕ→D) (n : ℕ) :
    splicePrefix P x y n=applyPairSplices P ((List.range n).map (fun i=>(x i,y i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [splicePrefix,ih,List.range_succ,List.map_append,applyPairSplices_append]
      rfl
end PlanarHom.FinitePermutationCycles

namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 def cellPairs (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f) : List (Dart f×Dart f) :=
  (List.range (sharedPred f i+1)).map (fun j =>
    (extendBoundaryPath (sharedPred f i) (oldMarker f hf i) j,
      extendBoundaryPath (sharedPred f i) (newMarker f i) j))

 def prefixPairs (f : NumericFormula) (hf : NumericValid f) : ℕ→List (Dart f×Dart f)
  | 0 => []
  | k+1 => if hk : k<(canvas f).length then prefixPairs f hf k++cellPairs f hf ⟨k,hk⟩ else prefixPairs f hf k

 def finalPairs (f : NumericFormula) (hf : NumericValid f) : List (Dart f×Dart f) :=
  prefixPairs f hf (canvas f).length

 theorem spliceCell_eq_applyPairSplices (f : NumericFormula) (hf : NumericValid f)
    (P : Equiv.Perm (Dart f)) (i : Canvas.Index f) :
    spliceCell f hf P i=applyPairSplices P (cellPairs f hf i) :=
  splicePrefix_eq_applyPairSplices _ _ _ _

 theorem prefixFace_eq_applyPairSplices (f : NumericFormula) (hf : NumericValid f) (n : ℕ) :
    prefixFace f hf n=applyPairSplices (baseFace f) (prefixPairs f hf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [prefixFace,prefixPairs]
      split_ifs with hn
      · rw [ih,spliceCell_eq_applyPairSplices,applyPairSplices_append]
      · exact ih

 theorem finalFace_eq_applyPairSplices (f : NumericFormula) (hf : NumericValid f) :
    finalFace f hf=applyPairSplices (baseFace f) (finalPairs f hf) :=
  prefixFace_eq_applyPairSplices f hf _

 theorem finalFace_untouched (f : NumericFormula) (hf : NumericValid f) (a : Dart f)
    (ha : a∉pairMarkers (finalPairs f hf)) : finalFace f hf a=baseFace f a := by
  rw [finalFace_eq_applyPairSplices]
  exact applyPairSplices_untouched _ _ _ ha

 theorem finalFace_first (f : NumericFormula) (hf : NumericValid f)
    (hn : (pairMarkers (finalPairs f hf)).Nodup) (p : Dart f×Dart f) (hp : p∈finalPairs f hf) :
    finalFace f hf p.1=baseFace f p.2 := by
  rw [finalFace_eq_applyPairSplices]
  exact applyPairSplices_first _ _ hn p hp

 theorem finalFace_second (f : NumericFormula) (hf : NumericValid f)
    (hn : (pairMarkers (finalPairs f hf)).Nodup) (p : Dart f×Dart f) (hp : p∈finalPairs f hf) :
    finalFace f hf p.2=baseFace f p.1 := by
  rw [finalFace_eq_applyPairSplices]
  exact applyPairSplices_second _ _ hn p hp
end PlanarHom.ColoringEmitter.FramedCanvas
