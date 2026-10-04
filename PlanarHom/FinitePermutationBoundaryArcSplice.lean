import PlanarHom.FinitePermutationBoundaryPathGluing

/-! NEW arbitrary-gap boundary splicing. Chosen boundary vertices may be only
an ordered subsequence of the exterior cycle; all intervening old vertices and
edges remain. The face increment is derived from the two surviving arcs. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {D : Type} [Fintype D]

structure MarkedBoundaryArc (P : Equiv.Perm D) (x y : ℕ→D) (t : ℕ) (a b : D) where
  length : ℕ
  positive : 0<length
  endpoint : P^[length] a=b
  interior : ∀ i, 0 < i → i < length → ∀ j < t, P^[i] a ≠ x j ∧ P^[i] a ≠ y j

 theorem splicePrefix_unjoined_arc (P : Equiv.Perm D) (x y : ℕ→D) {t k : ℕ}
    (hk : k≤t) (a b : D) (arc : MarkedBoundaryArc P x y t a b)
    (ha : ∀i<k,a≠x i ∧ a≠y i) :
    (splicePrefix P x y k)^[arc.length] a=b := by
  have hh:=orbitPrefix_of_same_steps P (splicePrefix P x y k) a arc.length (by
    intro i hi
    apply splicePrefix_untouched
    intro j hj
    by_cases hz : i=0
    · subst i
      exact ha j hj
    · exact arc.interior i (by omega) hi j (by omega))
  exact hh.1.trans arc.endpoint

 theorem splicePrefix_joined_arc (P : Equiv.Perm D) (x y : ℕ→D) {t k j : ℕ}
    (hd : DistinctPathMarkers x y t) (hk : k≤t) (hj : j<k)
    (b : D) (arc : MarkedBoundaryArc P x y t (x j) b) :
    (splicePrefix P x y k)^[arc.length] (y j)=b := by
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt arc.positive)
  have hh:=splicePrefix_arc P x y k (P (x j)) m (by
    intro i hi s hs
    have h:=arc.interior (i+1) (by omega) (by omega) s (by omega)
    simpa only [Function.iterate_succ_apply] using h)
  rw [hm,Function.iterate_succ_apply,splicePrefix_y_joined P x y hd hk hj,hh.1]
  simpa only [hm,Function.iterate_succ_apply] using arc.endpoint

 theorem splicePrefix_next_sameCycle_arcs (P : Equiv.Perm D) (x y : ℕ→D) {t k : ℕ}
    (hd : DistinctPathMarkers x y t) (hk0 : 0<k) (hk : k<t)
    (left : MarkedBoundaryArc P x y t (x (k-1)) (x k))
    (right : MarkedBoundaryArc P x y t (y k) (y (k-1))) :
    (splicePrefix P x y k).SameCycle (x k) (y k) := by
  have hR:=splicePrefix_unjoined_arc P x y (by omega : k≤t) (y k) (y (k-1)) right (by
    intro i hi
    exact ⟨(hd.2.2 i (by omega) k hk).symm,fun he=>by have := hd.2.1 k hk i (by omega) he; omega⟩)
  have hL:=splicePrefix_joined_arc P x y hd (by omega : k≤t) (by omega : k-1<k) (x k) left
  have hr:=sameCycle_iterate (splicePrefix P x y k) (y k) right.length
  have hl:=sameCycle_iterate (splicePrefix P x y k) (y (k-1)) left.length
  rw [hR] at hr
  rw [hL] at hl
  exact (hr.trans hl).symm

 theorem count_splicePrefix_arcs (P : Equiv.Perm D) (x y : ℕ→D) (n : ℕ)
    (hd : DistinctPathMarkers x y (n+1)) (hsep : ¬P.SameCycle (x 0) (y 0))
    (left : ∀i,i<n→MarkedBoundaryArc P x y (n+1) (x i) (x (i+1)))
    (right : ∀i,i<n→MarkedBoundaryArc P x y (n+1) (y (i+1)) (y i)) :
    count (splicePrefix P x y (n+1))+1=count P+n := by
  have main : ∀k,k≤n→count (splicePrefix P x y (k+1))+1=count P+k := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [splicePrefix,Nat.add_zero] using count_swap_of_separate P (x 0) (y 0) hsep
    | succ k ih =>
        intro hk
        have hsc:=splicePrefix_next_sameCycle_arcs P x y hd (by omega : 0<k+1) (by omega : k+1<n+1)
          (by simpa using left k (by omega)) (by simpa using right k (by omega))
        have hc:=count_swap_of_same (splicePrefix P x y (k+1)) (x (k+1)) (y (k+1))
          (hd.2.2 _ (by omega) _ (by omega)) hsc
        have hi:=ih (by omega)
        change count (swapInput (splicePrefix P x y (k+1)) (x (k+1)) (y (k+1)))+1=count P+(k+1)
        omega
  exact main n (le_refl _)

end PlanarHom.FinitePermutationCycles
