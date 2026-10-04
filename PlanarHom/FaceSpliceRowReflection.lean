import PlanarHom.ClosingBlocksFaceApplication
import PlanarHom.DisjointFaceSpliceApplication
import PlanarHom.PlanarityLRFacePermutation

/-! Pointwise reflection of a disjoint face-splice program into actual rows.
The premises describe literal one-block/two-block vertex words and their local
successors; they do not assert the resulting global permutation equality. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type} [Fintype E] {G : MultiGraph V E}

 theorem face_eq_splices_of_rows (R : RotationRows G) (F : Equiv.Perm (Dart E))
    (ps : List (Dart E×Dart E)) (hn : (pairMarkers ps).Nodup)
    (hhost : ∀p∈ps,(G.dartPair (reversePerm E p.1)).1=(G.dartPair (reversePerm E p.2)).1)
    (huniq : ∀p∈ps,∀q∈ps,
      (G.dartPair (reversePerm E p.1)).1=(G.dartPair (reversePerm E q.1)).1 → p=q)
    (hsingle : ∀v,(¬∃p∈ps,(G.dartPair (reversePerm E p.1)).1=v) →
      ∀a∈R.row v,(R.row v).formPerm a=(F*reversePerm E) a)
    (hpaired : ∀p∈ps,∃xs ys : List (Dart E),
      R.row (G.dartPair (reversePerm E p.1)).1=
        (xs++[reversePerm E p.2])++(ys++[reversePerm E p.1]) ∧
      (∀a∈xs++[reversePerm E p.2],(F*reversePerm E) a=(xs++[reversePerm E p.2]).formPerm a) ∧
      (∀a∈ys++[reversePerm E p.1],(F*reversePerm E) a=(ys++[reversePerm E p.1]).formPerm a)) :
    R.facePerm=applyPairSplices F ps := by
  have hJJ : (F*reversePerm E)*reversePerm E=F := by
    apply Equiv.ext
    rintro ⟨e,b⟩
    simp [Equiv.Perm.mul_apply,reversePerm]
  apply Equiv.ext
  intro z
  let v := (G.dartPair (reversePerm E z)).1
  have hzmem : reversePerm E z∈R.row v := (R.mem _ _).mpr rfl
  change (R.row v).formPerm (reversePerm E z)=applyPairSplices F ps z
  by_cases hp : ∃p∈ps,(G.dartPair (reversePerm E p.1)).1=v
  · obtain ⟨p,hp,hpv⟩ := hp
    obtain ⟨xs,ys,hrow,hl,hr⟩ := hpaired p hp
    have hvrow : R.row v=(xs++[reversePerm E p.2])++(ys++[reversePerm E p.1]) := by
      rw [←hpv]
      exact hrow
    have hnd := R.nodup v
    rw [hvrow] at hnd hzmem ⊢
    have hb := closingBlocks_face_apply (F*reversePerm E) (reversePerm E) xs ys
      (reversePerm E p.2) (reversePerm E p.1) z (fun a ha hb => (List.nodup_append.mp hnd).2.2 a ha a hb rfl) hl hr hzmem
    rw [hJJ,Equiv.symm_apply_apply,Equiv.symm_apply_apply] at hb
    simp only [Equiv.Perm.mul_apply] at hb
    rw [hb]
    by_cases hz1 : z=p.1
    · subst z
      rw [swapInput_b,applyPairSplices_first F ps hn p hp]
    · by_cases hz2 : z=p.2
      · subst z
        rw [swapInput_a,applyPairSplices_second F ps hn p hp]
      · have hnot : z∉pairMarkers ps := by
          intro hm
          obtain ⟨q,hq,hzq⟩ := List.mem_flatMap.mp hm
          have hchoices : z=q.1 ∨ z=q.2 := by simpa using hzq
          have hqv : (G.dartPair (reversePerm E q.1)).1=v := by
            rcases hchoices with h | h
            · rw [←h]
            · rw [hhost q hq,←h]
          have hpq := huniq p hp q hq (hpv.trans hqv.symm)
          subst q
          exact hchoices.elim hz1 hz2
        rw [applyPairSplices_untouched F ps z hnot]
        simp only [swapInput,Equiv.trans_apply]
        rw [@Equiv.swap_apply_of_ne_of_ne (Dart E) (Classical.decEq _) p.2 p.1 z hz2 hz1]
  · have hnot : z∉pairMarkers ps := by
      intro hm
      obtain ⟨q,hq,hzq⟩ := List.mem_flatMap.mp hm
      have hchoices : z=q.1 ∨ z=q.2 := by simpa using hzq
      apply hp
      refine ⟨q,hq,?_⟩
      rcases hchoices with h | h
      · rw [←h]
      · rw [hhost q hq,←h]
    rw [hsingle v hp _ hzmem,applyPairSplices_untouched F ps z hnot]
    change ((F*reversePerm E)*reversePerm E) z=F z
    rw [hJJ]
end PlanarHom.FinitePermutationCycles
