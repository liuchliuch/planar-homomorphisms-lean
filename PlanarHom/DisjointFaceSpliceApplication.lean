import PlanarHom.FinitePermutationSwapBound

/-! Pointwise semantics of a literal sequence of disjoint face-arrow swaps.
Every named pair exchanges its two original successors; all other arrows stay
unchanged, independently of the order in which the pairs are processed. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D]

 def pairMarkers (ps : List (D×D)) : List D := ps.flatMap (fun p => [p.1,p.2])
 def applyPairSplices (P : Equiv.Perm D) (ps : List (D×D)) : Equiv.Perm D :=
  ps.foldl (fun Q p=>swapInput Q p.1 p.2) P

 @[simp] theorem pairMarkers_nil : pairMarkers ([] : List (D×D))=[] := rfl
 @[simp] theorem pairMarkers_cons (p : D×D) (ps : List (D×D)) :
    pairMarkers (p::ps)=p.1::p.2::pairMarkers ps := rfl

 theorem first_mem_pairMarkers {p : D×D} {ps : List (D×D)} (hp : p∈ps) : p.1∈pairMarkers ps :=
  List.mem_flatMap.mpr ⟨p,hp,by simp⟩
 theorem second_mem_pairMarkers {p : D×D} {ps : List (D×D)} (hp : p∈ps) : p.2∈pairMarkers ps :=
  List.mem_flatMap.mpr ⟨p,hp,by simp⟩

 theorem applyPairSplices_untouched (P : Equiv.Perm D) (ps : List (D×D))
    (a : D) (ha : a∉pairMarkers ps) : applyPairSplices P ps a=P a := by
  induction ps generalizing P with
  | nil => rfl
  | cons p ps ih =>
      simp only [pairMarkers_cons,List.mem_cons,not_or] at ha
      change applyPairSplices (swapInput P p.1 p.2) ps a=P a
      rw [ih _ ha.2.2]
      simp only [swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne ha.1 ha.2.1]

 theorem applyPairSplices_first (P : Equiv.Perm D) (ps : List (D×D))
    (hn : (pairMarkers ps).Nodup) (p : D×D) (hp : p∈ps) :
    applyPairSplices P ps p.1=P p.2 := by
  induction ps generalizing P with
  | nil => simp at hp
  | cons q ps ih =>
      have hq : q.1∉q.2::pairMarkers ps ∧ (q.2::pairMarkers ps).Nodup := List.nodup_cons.mp hn
      have ht : q.2∉pairMarkers ps ∧ (pairMarkers ps).Nodup := List.nodup_cons.mp hq.2
      rcases List.mem_cons.mp hp with he | hp
      · subst p
        change applyPairSplices (swapInput P q.1 q.2) ps q.1=P q.2
        rw [applyPairSplices_untouched _ _ _ (fun h => hq.1 (List.mem_cons_of_mem _ h)),swapInput_a]
      · change applyPairSplices (swapInput P q.1 q.2) ps p.1=P p.2
        rw [ih _ ht.2 hp]
        have hm := second_mem_pairMarkers hp
        have h1 : p.2≠q.1 := by intro he; rw [he] at hm; exact hq.1 (List.mem_cons_of_mem _ hm)
        have h2 : p.2≠q.2 := by intro he; rw [he] at hm; exact ht.1 hm
        simp only [swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne h1 h2]

 theorem applyPairSplices_second (P : Equiv.Perm D) (ps : List (D×D))
    (hn : (pairMarkers ps).Nodup) (p : D×D) (hp : p∈ps) :
    applyPairSplices P ps p.2=P p.1 := by
  induction ps generalizing P with
  | nil => simp at hp
  | cons q ps ih =>
      have hq : q.1∉q.2::pairMarkers ps ∧ (q.2::pairMarkers ps).Nodup := List.nodup_cons.mp hn
      have ht : q.2∉pairMarkers ps ∧ (pairMarkers ps).Nodup := List.nodup_cons.mp hq.2
      rcases List.mem_cons.mp hp with he | hp
      · subst p
        change applyPairSplices (swapInput P q.1 q.2) ps q.2=P q.1
        rw [applyPairSplices_untouched _ _ _ ht.1,swapInput_b]
      · change applyPairSplices (swapInput P q.1 q.2) ps p.2=P p.1
        rw [ih _ ht.2 hp]
        have hm := first_mem_pairMarkers hp
        have h1 : p.1≠q.1 := by intro he; rw [he] at hm; exact hq.1 (List.mem_cons_of_mem _ hm)
        have h2 : p.1≠q.2 := by intro he; rw [he] at hm; exact ht.1 hm
        simp only [swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne h1 h2]
end PlanarHom.FinitePermutationCycles
