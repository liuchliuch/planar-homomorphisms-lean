import PlanarHom.FinitePermutationBoundaryPathSplice

/-! NEW exact complementary exterior word after the boundary path splice.
Empty complementary arcs are allowed. The word records the order needed by
later gluing steps, rather than only asserting that markers are cofacial. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {D : Type} [Fintype D]

 theorem orbitPrefix_of_same_steps (P Q : Equiv.Perm D) (a : D) (n : ℕ)
    (h : ∀i<n,Q (P^[i] a)=P (P^[i] a)) :
    Q^[n] a=P^[n] a ∧ orbitPrefix Q n a=orbitPrefix P n a := by
  have hi : ∀i,i≤n→Q^[i] a=P^[i] a := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        intro hin
        rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih (by omega),h i (by omega)]
  refine ⟨hi n (le_refl _),?_⟩
  apply List.map_congr_left
  intro i him
  exact hi i (Nat.le_of_lt (List.mem_range.mp him))

 theorem splicePrefix_arc (P : Equiv.Perm D) (x y : ℕ→D) (t : ℕ) (a : D) (n : ℕ)
    (h : ∀i<n,∀j<t,P^[i] a≠x j ∧ P^[i] a≠y j) :
    (splicePrefix P x y t)^[n] a=P^[n] a ∧
      orbitPrefix (splicePrefix P x y t) n a=orbitPrefix P n a :=
  orbitPrefix_of_same_steps P (splicePrefix P x y t) a n
    (fun i hi=>splicePrefix_untouched P x y t _ (h i hi))

 def splicedExteriorWord (P : Equiv.Perm D) (x y : ℕ→D) (n l r : ℕ) : List D :=
  [x 0]++orbitPrefix P r (P (y 0))++[y n]++orbitPrefix P l (P (x n))

 theorem splicePrefix_exterior_word (P : Equiv.Perm D) (x y : ℕ→D) (n l r : ℕ)
    (hd : DistinctPathMarkers x y (n+1))
    (hl : P^[l] (P (x n))=x 0) (hr : P^[r] (P (y 0))=y n)
    (hal : ∀i<l,∀j<n+1,P^[i] (P (x n))≠x j ∧ P^[i] (P (x n))≠y j)
    (har : ∀i<r,∀j<n+1,P^[i] (P (y 0))≠x j ∧ P^[i] (P (y 0))≠y j) :
    (splicePrefix P x y (n+1))^[1+r+1+l] (x 0)=x 0 ∧
      orbitPrefix (splicePrefix P x y (n+1)) (1+r+1+l) (x 0)=splicedExteriorWord P x y n l r := by
  let S:=splicePrefix P x y (n+1)
  have hx : S (x 0)=P (y 0) := splicePrefix_x_joined P x y hd (le_refl _) (by omega)
  have hy : S (y n)=P (x n) := splicePrefix_y_joined P x y hd (le_refl _) (by omega)
  have hL:=splicePrefix_arc P x y (n+1) (P (x n)) l hal
  have hR:=splicePrefix_arc P x y (n+1) (P (y 0)) r har
  have hLe : S^[l] (P (x n))=x 0 := hL.1.trans hl
  have hRe : S^[r] (P (y 0))=y n := hR.1.trans hr
  constructor
  · change S^[1+r+1+l] (x 0)=x 0
    rw [show 1+r+1+l=l+1+r+1 by omega,Function.iterate_succ_apply,hx,
      Function.iterate_add_apply, hRe,Function.iterate_succ_apply,hy,hLe]
  · change orbitPrefix S (1+r+1+l) (x 0)=_
    rw [show 1+r+1+l=1+(r+(1+l)) by omega,orbitPrefix_add]
    simp only [orbitPrefix, List.range_one,List.map_singleton,Function.iterate_zero_apply,
      Function.iterate_one] at hx ⊢
    change [x 0]++orbitPrefix S (r+(1+l)) (S (x 0))=_
    rw [hx,orbitPrefix_add,hRe,hR.2,orbitPrefix_add]
    change [x 0]++(orbitPrefix P r (P (y 0))++([y n]++orbitPrefix S l (S (y n))))=_
    rw [hy,hL.2]
    simp only [splicedExteriorWord,List.append_assoc]

 theorem splicePrefix_exterior_period (P : Equiv.Perm D) (x y : ℕ→D) (n l r : ℕ)
    (hd : DistinctPathMarkers x y (n+1))
    (hl : P^[l] (P (x n))=x 0) (hr : P^[r] (P (y 0))=y n)
    (hal : ∀i<l,∀j<n+1,P^[i] (P (x n))≠x j ∧ P^[i] (P (x n))≠y j)
    (har : ∀i<r,∀j<n+1,P^[i] (P (y 0))≠x j ∧ P^[i] (P (y 0))≠y j)
    (hn : (splicedExteriorWord P x y n l r).Nodup) :
    Function.minimalPeriod (splicePrefix P x y (n+1)) (x 0)=1+r+1+l ∧
      orbitPrefix (splicePrefix P x y (n+1))
        (Function.minimalPeriod (splicePrefix P x y (n+1)) (x 0)) (x 0)=splicedExteriorWord P x y n l r := by
  have hh:=splicePrefix_exterior_word P x y n l r hd hl hr hal har
  have hp:=period_eq_of_prefix_nodup (splicePrefix P x y (n+1)) (x 0) (1+r+1+l) (by omega) hh.1
    (hh.2.symm ▸ hn)
  exact ⟨hp,by rw [hp]; exact hh.2⟩

end PlanarHom.FinitePermutationCycles
