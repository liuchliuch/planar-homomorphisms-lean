import PlanarHom.FinitePermutationSwapSplit
import PlanarHom.FinitePermutationArrowSubdivision
import PlanarHom.FinitePermutationReturnWords

/-! NEW exact face-arrow splice along two oppositely directed simple boundary
paths. Each join after the first produces a literal digon; no repeated
cofaciality premise is required. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D]

 def splicePrefix (P : Equiv.Perm D) (x y : ℕ→D) : ℕ→Equiv.Perm D
  | 0 => P
  | k+1 => swapInput (splicePrefix P x y k) (x k) (y k)

/-- All named path markers are distinct. The two rows may otherwise have
arbitrary lengths and arbitrary additional face cycles. -/
def DistinctPathMarkers (x y : ℕ→D) (t : ℕ) : Prop :=
  (∀i<t,∀j<t,x i=x j→i=j) ∧
  (∀i<t,∀j<t,y i=y j→i=j) ∧
  (∀i<t,∀j<t,x i≠y j)

 theorem splicePrefix_untouched (P : Equiv.Perm D) (x y : ℕ→D) (k : ℕ) (a : D)
    (h : ∀i<k,a≠x i ∧ a≠y i) : splicePrefix P x y k a=P a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [splicePrefix,swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne (h k (by omega)).1 (h k (by omega)).2]
      exact ih (fun i hi=>h i (by omega))

 theorem splicePrefix_x_unjoined (P : Equiv.Perm D) (x y : ℕ→D) {t k j : ℕ}
    (hd : DistinctPathMarkers x y t) (hj : j<t) (hk : k≤j) :
    splicePrefix P x y k (x j)=P (x j) := by
  apply splicePrefix_untouched
  intro i hi
  exact ⟨fun he=>by have := hd.1 j hj i (by omega) he; omega,hd.2.2 j hj i (by omega)⟩

 theorem splicePrefix_y_unjoined (P : Equiv.Perm D) (x y : ℕ→D) {t k j : ℕ}
    (hd : DistinctPathMarkers x y t) (hj : j<t) (hk : k≤j) :
    splicePrefix P x y k (y j)=P (y j) := by
  apply splicePrefix_untouched
  intro i hi
  exact ⟨(hd.2.2 i (by omega) j hj).symm,fun he=>by have := hd.2.1 j hj i (by omega) he; omega⟩

 theorem splicePrefix_x_joined (P : Equiv.Perm D) (x y : ℕ→D) {t k j : ℕ}
    (hd : DistinctPathMarkers x y t) (hk : k≤t) (hj : j<k) :
    splicePrefix P x y k (x j)=P (y j) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases he : j=k
      · subst j
        rw [splicePrefix,swapInput_a]
        exact splicePrefix_y_unjoined P x y hd (by omega) (le_refl _)
      · have hjk : j<k := by omega
        rw [splicePrefix,swapInput,Equiv.trans_apply,
          Equiv.swap_apply_of_ne_of_ne
            (show x j≠x k from fun hh=>he (hd.1 j (by omega) k (by omega) hh))
            (hd.2.2 j (by omega) k (by omega))]
        exact ih (by omega) hjk

 theorem splicePrefix_y_joined (P : Equiv.Perm D) (x y : ℕ→D) {t k j : ℕ}
    (hd : DistinctPathMarkers x y t) (hk : k≤t) (hj : j<k) :
    splicePrefix P x y k (y j)=P (x j) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases he : j=k
      · subst j
        rw [splicePrefix,swapInput_b]
        exact splicePrefix_x_unjoined P x y hd (by omega) (le_refl _)
      · have hjk : j<k := by omega
        rw [splicePrefix,swapInput,Equiv.trans_apply,
          Equiv.swap_apply_of_ne_of_ne (hd.2.2 k (by omega) j (by omega)).symm
            (show y j≠y k from fun hh=>he (hd.2.1 j (by omega) k (by omega) hh))]
        exact ih (by omega) hjk

 theorem splicePrefix_next_sameCycle (P : Equiv.Perm D) (x y : ℕ→D) {t k : ℕ}
    (hd : DistinctPathMarkers x y t) (hk0 : 0<k) (hk : k<t)
    (hx : P (x (k-1))=x k) (hy : P (y k)=y (k-1)) :
    (splicePrefix P x y k).SameCycle (x k) (y k) := by
  have h₁ : (splicePrefix P x y k).SameCycle (y k) (y (k-1)) := by
    have h := Equiv.Perm.SameCycle.rfl (f:=splicePrefix P x y k) (x:=y k) |>.apply_right
    rwa [splicePrefix_y_unjoined P x y hd hk (le_refl _),hy] at h
  have h₂ : (splicePrefix P x y k).SameCycle (y (k-1)) (x k) := by
    have h := Equiv.Perm.SameCycle.rfl (f:=splicePrefix P x y k) (x:=y (k-1)) |>.apply_right
    rwa [splicePrefix_y_joined P x y hd (by omega) (by omega),hx] at h
  exact (h₁.trans h₂).symm

 theorem count_splicePrefix (P : Equiv.Perm D) (x y : ℕ→D) (n : ℕ)
    (hd : DistinctPathMarkers x y (n+1))
    (hsep : ¬P.SameCycle (x 0) (y 0))
    (hx : ∀i<n,P (x i)=x (i+1)) (hy : ∀i<n,P (y (i+1))=y i) :
    count (splicePrefix P x y (n+1))+1=count P+n := by
  have main : ∀k,k≤n→count (splicePrefix P x y (k+1))+1=count P+k := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [splicePrefix,Nat.add_zero] using count_swap_of_separate P (x 0) (y 0) hsep
    | succ k ih =>
        intro hk
        have hsc := splicePrefix_next_sameCycle P x y hd (by omega : 0<k+1) (by omega : k+1<n+1)
          (by simpa using hx k (by omega)) (by simpa using hy k (by omega))
        have hc := count_swap_of_same (splicePrefix P x y (k+1)) (x (k+1)) (y (k+1))
          (hd.2.2 _ (by omega) _ (by omega)) hsc
        have hi := ih (by omega)
        change count (swapInput (splicePrefix P x y (k+1)) (x (k+1)) (y (k+1)))+1=count P+(k+1)
        omega
  exact main n (le_refl _)

 theorem splicePrefix_digon (P : Equiv.Perm D) (x y : ℕ→D) (n : ℕ)
    (hd : DistinctPathMarkers x y (n+1))
    (hx : ∀i<n,P (x i)=x (i+1)) (hy : ∀i<n,P (y (i+1))=y i)
    (i : ℕ) (hi : i<n) :
    splicePrefix P x y (n+1) (x (i+1))=y i ∧
      splicePrefix P x y (n+1) (y i)=x (i+1) := by
  rw [splicePrefix_x_joined P x y hd (le_refl _) (by omega),
    splicePrefix_y_joined P x y hd (le_refl _) (by omega),hx i hi,hy i hi]
  exact ⟨rfl,rfl⟩

end PlanarHom.FinitePermutationCycles
