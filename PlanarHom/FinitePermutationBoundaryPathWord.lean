import PlanarHom.FinitePermutationBoundaryPathGluing

/-! NEW exact two-input exterior cycle word after consecutive path gluing. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A B : Type} [Fintype A] [Fintype B]

 theorem boundary_sum_iterate_left (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (a : A) :
    (Equiv.sumCongr P Q)^[n] (.inl a)=.inl (P^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

 theorem boundary_sum_iterate_right (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (b : B) :
    (Equiv.sumCongr P Q)^[n] (.inr b)=.inr (Q^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

 theorem orbitPrefix_sum_left (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (a : A) :
    orbitPrefix (Equiv.sumCongr P Q) n (.inl a)=(orbitPrefix P n a).map Sum.inl := by
  simp only [orbitPrefix,List.map_map,Function.comp_def,boundary_sum_iterate_left]

 theorem orbitPrefix_sum_right (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (b : B) :
    orbitPrefix (Equiv.sumCongr P Q) n (.inr b)=(orbitPrefix Q n b).map Sum.inr := by
  simp only [orbitPrefix,List.map_map,Function.comp_def,boundary_sum_iterate_right]

 theorem boundaryPathSplice_exterior (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n l r : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (hl : P^[l] (P (x n))=x 0) (hr : Q^[r] (Q (y 0))=y n)
    (hal : ∀i<l,∀j<n+1,P^[i] (P (x n))≠x j)
    (har : ∀i<r,∀j<n+1,Q^[i] (Q (y 0))≠y j) :
    Function.minimalPeriod (boundaryPathSplice P Q x y (n+1)) (.inl (x 0))=1+r+1+l ∧
      orbitPrefix (boundaryPathSplice P Q x y (n+1))
        (Function.minimalPeriod (boundaryPathSplice P Q x y (n+1)) (.inl (x 0))) (.inl (x 0))=
          [.inl (x 0)]++(orbitPrefix Q r (Q (y 0))).map Sum.inr++[.inr (y n)]++
            (orbitPrefix P l (P (x n))).map Sum.inl := by
  have hL : (Equiv.sumCongr P Q)^[l] (Equiv.sumCongr P Q (.inl (x n)))=Sum.inl (x 0) := by
    simpa only [Equiv.sumCongr_apply,Sum.map_inl,boundary_sum_iterate_left] using congrArg Sum.inl hl
  have hR : (Equiv.sumCongr P Q)^[r] (Equiv.sumCongr P Q (.inr (y 0)))=Sum.inr (y n) := by
    simpa only [Equiv.sumCongr_apply,Sum.map_inr,boundary_sum_iterate_right] using congrArg Sum.inr hr
  have hLa : ∀i<l,∀j<n+1,(Equiv.sumCongr P Q)^[i] (Equiv.sumCongr P Q (.inl (x n)))≠Sum.inl (x j) ∧
      (Equiv.sumCongr P Q)^[i] (Equiv.sumCongr P Q (.inl (x n)))≠Sum.inr (y j) := by
    intro i hi j hj
    simp only [Equiv.sumCongr_apply,Sum.map_inl,boundary_sum_iterate_left]
    exact ⟨fun h=>hal i hi j hj (Sum.inl.inj h),Sum.inl_ne_inr⟩
  have hRa : ∀i<r,∀j<n+1,(Equiv.sumCongr P Q)^[i] (Equiv.sumCongr P Q (.inr (y 0)))≠Sum.inl (x j) ∧
      (Equiv.sumCongr P Q)^[i] (Equiv.sumCongr P Q (.inr (y 0)))≠Sum.inr (y j) := by
    intro i hi j hj
    simp only [Equiv.sumCongr_apply,Sum.map_inr,boundary_sum_iterate_right]
    exact ⟨Sum.inr_ne_inl,fun h=>har i hi j hj (Sum.inr.inj h)⟩
  have hh:=splicePrefix_exterior_cycle (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) n l r
    (sum_path_markers x y (n+1) hxi hyi) (not_sameCycle_sum_cross P Q (x 0) (y 0)) hL hR hLa hRa
  simpa only [boundaryPathSplice,splicedExteriorWord,Function.comp_apply,Equiv.sumCongr_apply,
    Sum.map_inl,Sum.map_inr,orbitPrefix_sum_left,orbitPrefix_sum_right] using hh

/-- Extend a finite path only to expose the simple recursion used by the
splice; all theorems inspect indices strictly below the original length. -/
 def extendBoundaryPath (n : ℕ) {C : Type} (x : Fin (n+1)→C) (i : ℕ) : C :=
  x ⟨min i n,by omega⟩

@[simp] theorem extendBoundaryPath_at (n : ℕ) {C : Type} (x : Fin (n+1)→C) (i : Fin (n+1)) :
    extendBoundaryPath n x i.val=x i := by
  unfold extendBoundaryPath
  congr 1
  apply Fin.ext
  exact min_eq_left (by have := i.isLt; omega)

 theorem extendBoundaryPath_injective (n : ℕ) {C : Type} (x : Fin (n+1)→C) (hx : Function.Injective x) :
    ∀i<n+1,∀j<n+1,extendBoundaryPath n x i=extendBoundaryPath n x j→i=j := by
  intro i hi j hj he
  have hh:=hx he
  have hv:=congrArg Fin.val hh
  simpa only [min_eq_left (show i≤n by omega),min_eq_left (show j≤n by omega)] using hv

 def finiteBoundaryPathSplice (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ)
    (x : Fin (n+1)→A) (y : Fin (n+1)→B) : Equiv.Perm (A⊕B) :=
  boundaryPathSplice P Q (extendBoundaryPath n x) (extendBoundaryPath n y) (n+1)

 theorem finiteBoundaryPathSplice_count (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ)
    (x : Fin (n+1)→A) (y : Fin (n+1)→B) (hxi : Function.Injective x) (hyi : Function.Injective y)
    (hx : ∀i:Fin n,P (x i.castSucc)=x i.succ) (hy : ∀i:Fin n,Q (y i.succ)=y i.castSucc) :
    count (finiteBoundaryPathSplice P Q n x y)+1=count P+count Q+n := by
  apply boundaryPathSplice_count P Q _ _ n
    (extendBoundaryPath_injective n x hxi) (extendBoundaryPath_injective n y hyi)
  · intro i hi
    have hh:=hx ⟨i,hi⟩
    simpa only [←extendBoundaryPath_at n x,Fin.val_succ] using hh
  · intro i hi
    have hh:=hy ⟨i,hi⟩
    simpa only [←extendBoundaryPath_at n y,Fin.val_succ] using hh

end PlanarHom.FinitePermutationCycles
