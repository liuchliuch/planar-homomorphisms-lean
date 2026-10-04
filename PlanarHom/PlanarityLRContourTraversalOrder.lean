import PlanarHom.PlanarityLRContourKeyOrder
import PlanarHom.PlanarityLRContourBackEvents

/-! NEW strict order of the actual full contour traversal from its concrete
root-row start, followed by its outward-back projection. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 def dfsContourWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
   (List.range (Function.minimalPeriod (dfsContour g hg bits) a)).map
     (fun n=>(dfsContour g hg bits)^[n] a)

 theorem dfsContour_iterate_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    componentRoot g (dartHost g ((dfsContour g hg bits)^[n] a))=componentRoot g (dartHost g a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',dfsContourForRows_componentRoot,ih]

 theorem contourKey_iterate_lt_succ (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a))
    (i : ℕ) (hi : i+1<Function.minimalPeriod (dfsContour g hg bits) a) :
    contourKey g bits (eraseDart ((dfsContour g hg bits)^[i] a))<
      contourKey g bits (eraseDart ((dfsContour g hg bits)^[i+1] a)) := by
  have hstep:=contourKey_step g hg bits (a := eraseDart ((dfsContour g hg bits)^[i] a))
    ((dfsContour g hg bits)^[i] a).1.isLt
  have he : eraseDart ((dfsContour g hg bits)^[i+1] a)=
      rawContourStep g bits (eraseDart ((dfsContour g hg bits)^[i] a)) := by
    rw [Function.iterate_succ_apply',dfsContour_erase]
  rw [← he] at hstep
  rcases hstep with hgood | hroot
  · exact hgood
  · have hr:componentRoot g (PlanarityRotationCode.host g (eraseDart ((dfsContour g hg bits)^[i+1] a)))=
        componentRoot g (PlanarityRotationCode.host g (eraseDart a)) :=
      dfsContour_iterate_componentRoot g hg bits a (i+1)
    have hraw:=rootFirst_unique g hg bits ((dfsContour g hg bits)^[i+1] a).1.isLt a.1.isLt
      hroot hstart hr
    have htyped:=eraseDart_injective g hraw
    have hp : 0<Function.minimalPeriod (dfsContour g hg bits) a :=
      Function.minimalPeriod_pos_of_mem_periodicPts ((dfsContour g hg bits).injective.mem_periodicPts a)
    have hn := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hp).mp htyped
    omega

 theorem dfsContourWord_key_sorted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a)) :
    (dfsContourWord g hg bits a).Pairwise
      (fun b c=>contourKey g bits (eraseDart b)<contourKey g bits (eraseDart c)) := by
  have hlt : ∀j, j<Function.minimalPeriod (dfsContour g hg bits) a →
      ∀i, i<j → contourKey g bits (eraseDart ((dfsContour g hg bits)^[i] a))<
        contourKey g bits (eraseDart ((dfsContour g hg bits)^[j] a)) := by
    intro j
    induction j with
    | zero => intro hj i hi; omega
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hij | rfl
      · exact lt_trans (ih (by omega) i hij) (contourKey_iterate_lt_succ g hg bits a hstart j hj)
      · exact contourKey_iterate_lt_succ g hg bits a hstart i hj
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [dfsContourWord,List.length_map,List.length_range] at hi hj
  simpa only [dfsContourWord,List.getElem_map,List.getElem_range] using hlt j hj i hij

 theorem contourBackEvents_key_sorted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a)) :
    (contourBackEvents g hg bits a).Pairwise (fun e f=>
      contourKey g bits (PlanarityRotationCode.outward g e)<
      contourKey g bits (PlanarityRotationCode.outward g f)) := by
  have hs:=(dfsContourWord_key_sorted g hg bits a hstart).filter (fun b=>!(isTree g b.1.val))
  have hs':=hs.filter (outwardBackFlag g)
  apply List.pairwise_map.mpr
  apply hs'.imp_of_mem
  intro b c hb hc hbc
  have hbb : b=typedOutward g b.1 := by
    have hh : isBack g b.1.val=true ∧ b=typedOutward g b.1 := by
      simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact hh.2
  have hcc : c=typedOutward g c.1 := by
    have hh : isBack g c.1.val=true ∧ c=typedOutward g c.1 := by
      simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using (List.mem_filter.mp hc).2
    exact hh.2
  have heb : eraseDart b=PlanarityRotationCode.outward g b.1.val := by
    conv_lhs => rw [hbb]
    exact erase_typedOutward g b.1
  have hec : eraseDart c=PlanarityRotationCode.outward g c.1.val := by
    conv_lhs => rw [hcc]
    exact erase_typedOutward g c.1
  simpa only [heb,hec] using hbc

end PlanarHom.PlanarityLRRealization
