import PlanarHom.PlanarityLRContourBlockWords
import PlanarHom.PlanarityLRDrawnTree

/-! NEW occurrence-preserving transport between the original directions and
DFS-directed tree geometry. Literal row order and contour words are preserved. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

def dfsDartEquiv (g : MixedCode) : Equiv.Perm (Dart (Fin g.edges.length)) where
  toFun a := (a.1, if (typedOutward g a.1).2 then a.2 else !a.2)
  invFun a := (a.1, if (typedOutward g a.1).2 then a.2 else !a.2)
  left_inv a := by cases h : (typedOutward g a.1).2 <;> simp [h]
  right_inv a := by cases h : (typedOutward g a.1).2 <;> simp [h]

@[simp] theorem dfsDartEquiv_index (g : MixedCode) (a : Dart (Fin g.edges.length)) :
    (dfsDartEquiv g a).1=a.1 := rfl

@[simp] theorem dfsDartEquiv_reverse (g : MixedCode) (a : Dart (Fin g.edges.length)) :
    dfsDartEquiv g (reversePerm _ a)=reversePerm _ (dfsDartEquiv g a) := by
  cases h : (typedOutward g a.1).2 <;> simp [dfsDartEquiv,reversePerm,h]

@[simp] theorem dfsDartEquiv_outward (g : MixedCode) (e : Fin g.edges.length) :
    dfsDartEquiv g (typedOutward g e)=(e,true) := by
  apply Prod.ext
  · rfl
  · change (if (typedOutward g e).2 then (typedOutward g e).2 else !(typedOutward g e).2)=true
    cases (typedOutward g e).2 <;> rfl

@[simp] theorem dfsDartEquiv_symm (g : MixedCode) : (dfsDartEquiv g).symm=dfsDartEquiv g := rfl

theorem dfsDartEquiv_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) :
    ((dfsGraph g hg).dartPair (dfsDartEquiv g a)).1=((g.toMultiGraph hg).dartPair a).1 := by
  apply Fin.ext
  rw [←eraseDart_host g hg a]
  change _=dartHost g a
  obtain ⟨e,rfl | rfl⟩ := exists_typedOutward g a
  · rw [dfsDartEquiv_outward,dartHost_typedOutward]
    rfl
  · rw [dfsDartEquiv_reverse,dfsDartEquiv_outward,dartHost_reverse_typedOutward]
    rfl

namespace RotationRows
variable {V E : Type*} {G H : MultiGraph V E} [DecidableEq (Dart E)]

def pullDarts (rows : RotationRows H) (e : Equiv.Perm (Dart E))
    (hhost : ∀ a, (H.dartPair (e a)).1=(G.dartPair a).1) : RotationRows G where
  row v := (rows.row v).map e.symm
  nodup v := (rows.nodup v).map e.symm.injective
  mem v a := by
    rw [List.mem_map]
    constructor
    · rintro ⟨b,hb,he⟩
      have hba : b=e a := by rw [←he,e.apply_symm_apply]
      subst b
      exact (hhost a) ▸ ((rows.mem _ _).mp hb)
    · intro ha
      exact ⟨e a,(rows.mem _ _).mpr ((hhost a).trans ha),e.symm_apply_apply a⟩

theorem pullDarts_rotation (rows : RotationRows H) (e : Equiv.Perm (Dart E))
    (hhost : ∀ a, (H.dartPair (e a)).1=(G.dartPair a).1) (a : Dart E) :
    e ((rows.pullDarts e hhost).rotation a)=rows.rotation (e a) := by
  have ha : e a∈rows.row (G.dartPair a).1 := (rows.mem _ _).mpr (hhost a)
  have hh := map_formPerm_apply e.symm e.symm.injective (rows.row (G.dartPair a).1)
    (rows.nodup _) ha
  apply e.symm.injective
  simpa only [e.symm_apply_apply,rotation_apply,pullDarts,hhost] using hh
end RotationRows

def dfsPullRows (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) : RotationRows (g.toMultiGraph hg) :=
  rows.pullDarts (dfsDartEquiv g) (dfsDartEquiv_host g hg)

theorem dfsDartEquiv_contour (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) :
    dfsDartEquiv g (dfsContourForRows g hg (dfsPullRows g hg rows) a)=
      contourPermutation rows (fun e => isTree g e.val) (dfsDartEquiv g a) := by
  by_cases ha : isTree g a.1.val=true
  · rw [dfsContourForRows,contourPermutation_selected _ _ a ha,
      contourPermutation_selected _ _ _ ha,←dfsDartEquiv_reverse]
    exact rows.pullDarts_rotation _ _ _
  · have hp := Bool.eq_false_iff.mpr ha
    rw [dfsContourForRows,contourPermutation_port _ _ a hp,contourPermutation_port _ _ _ hp]
    exact rows.pullDarts_rotation _ _ _

theorem dfsDartEquiv_contour_iterate (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    dfsDartEquiv g ((dfsContourForRows g hg (dfsPullRows g hg rows))^[n] a)=
      (contourPermutation rows (fun e => isTree g e.val))^[n] (dfsDartEquiv g a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',dfsDartEquiv_contour,ih,Function.iterate_succ_apply']

theorem dfsDartEquiv_contour_period (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) :
    Function.minimalPeriod (dfsContourForRows g hg (dfsPullRows g hg rows)) a=
      Function.minimalPeriod (contourPermutation rows (fun e => isTree g e.val)) (dfsDartEquiv g a) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change _=a ↔ _=dfsDartEquiv g a
  rw [←dfsDartEquiv_contour_iterate]
  exact (dfsDartEquiv g).injective.eq_iff.symm

theorem dfsDartEquiv_contour_word (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) :
    (orbitPrefix (dfsContourForRows g hg (dfsPullRows g hg rows))
        (Function.minimalPeriod (dfsContourForRows g hg (dfsPullRows g hg rows)) a) a).map (dfsDartEquiv g)=
      orbitPrefix (contourPermutation rows (fun e => isTree g e.val))
        (Function.minimalPeriod (contourPermutation rows (fun e => isTree g e.val)) (dfsDartEquiv g a))
        (dfsDartEquiv g a) := by
  simp only [orbitPrefix,List.map_map,Function.comp_def,dfsDartEquiv_contour_iterate,dfsDartEquiv_contour_period]

/-- Reorienting occurrences retains the exact emitted contour port sequence. -/
theorem dfsDartEquiv_contour_ports (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) :
    (contourPortWord (dfsPullRows g hg rows) (fun e => isTree g e.val) a).map (dfsDartEquiv g)=
      contourPortWord rows (fun e => isTree g e.val) (dfsDartEquiv g a) := by
  have h := congrArg (List.filter (fun b : Dart (Fin g.edges.length) => !(isTree g b.1.val)))
    (dfsDartEquiv_contour_word g hg rows a)
  simpa only [List.filter_map,Function.comp_def,dfsDartEquiv_index,orbitPrefix,
    contourPortWord,dfsContourForRows] using h

end PlanarHom.PlanarityLRRealization
