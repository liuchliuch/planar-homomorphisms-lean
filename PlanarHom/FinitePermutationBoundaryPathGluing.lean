import PlanarHom.FinitePermutationBoundaryPathExterior

/-! NEW boundary-path gluing with a literal exterior cycle. The first-hit and
separate-input hypotheses imply the exterior word is simple, so its exact
minimal-period traversal is derived rather than supplied. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {D : Type} [Fintype D]

 theorem sameCycle_iterate (P : Equiv.Perm D) (a : D) (n : ℕ) : P.SameCycle a (P^[n] a) := by
  refine ⟨(n:ℤ),?_⟩
  simp only [zpow_natCast,Equiv.Perm.iterate_eq_pow]

 theorem orbitPrefix_nodup_of_first_hit (P : Equiv.Perm D) (a b : D) (n : ℕ)
    (hend : P^[n] a=b) (hfirst : ∀i<n,P^[i] a≠b) : (orbitPrefix P n a).Nodup := by
  apply orbitPrefix_nodup
  by_contra hn
  have hn' : Function.minimalPeriod P a<n := by omega
  have hp:=Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
  have hm : n%Function.minimalPeriod P a<n := (Nat.mod_lt _ hp).trans hn'
  apply hfirst _ hm
  rw [Function.iterate_mod_minimalPeriod_eq,hend]

 theorem splicedExteriorWord_nodup (P : Equiv.Perm D) (x y : ℕ→D) (n l r : ℕ)
    (hd : DistinctPathMarkers x y (n+1)) (hsep : ¬P.SameCycle (x 0) (y 0))
    (hl : P^[l] (P (x n))=x 0) (hr : P^[r] (P (y 0))=y n)
    (hal : ∀i<l,∀j<n+1,P^[i] (P (x n))≠x j ∧ P^[i] (P (x n))≠y j)
    (har : ∀i<r,∀j<n+1,P^[i] (P (y 0))≠x j ∧ P^[i] (P (y 0))≠y j) :
    (splicedExteriorWord P x y n l r).Nodup := by
  have hln:=orbitPrefix_nodup_of_first_hit P (P (x n)) (x 0) l hl (fun i hi=>(hal i hi 0 (by omega)).1)
  have hrn:=orbitPrefix_nodup_of_first_hit P (P (y 0)) (y n) r hr (fun i hi=>(har i hi n (by omega)).2)
  have hL (a) (ha:a∈orbitPrefix P l (P (x n))) : a≠x 0 ∧ a≠y n := by
    obtain ⟨i,hi,rfl⟩:=(mem_orbitPrefix _ _ _ _).mp ha
    exact ⟨(hal i hi 0 (by omega)).1,(hal i hi n (by omega)).2⟩
  have hR (a) (ha:a∈orbitPrefix P r (P (y 0))) : a≠x 0 ∧ a≠y n := by
    obtain ⟨i,hi,rfl⟩:=(mem_orbitPrefix _ _ _ _).mp ha
    exact ⟨(har i hi 0 (by omega)).1,(har i hi n (by omega)).2⟩
  have hcross (a) (ha:a∈orbitPrefix P l (P (x n)))
      (hb:a∈orbitPrefix P r (P (y 0))) : False := by
    obtain ⟨i,hi,hia⟩:=(mem_orbitPrefix _ _ _ _).mp ha
    obtain ⟨j,hj,hja⟩:=(mem_orbitPrefix _ _ _ _).mp hb
    have hx : P.SameCycle (x 0) a := by
      have hh := (sameCycle_iterate P (P (x n)) l).symm.trans (sameCycle_iterate P (P (x n)) i)
      rwa [hl,hia] at hh
    have hy : P.SameCycle (y 0) a := by
      have hh := (show P.SameCycle (y 0) (P (y 0)) from Equiv.Perm.SameCycle.rfl.apply_right).trans
        (sameCycle_iterate P (P (y 0)) j)
      rwa [hja] at hh
    exact hsep (hx.trans hy.symm)
  rw [splicedExteriorWord,List.singleton_append,List.append_assoc,List.singleton_append]
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    · exact (hR _ h).1 rfl
    · rcases List.mem_cons.mp h with h|h
      · exact hd.2.2 0 (by omega) n (by omega) h
      · exact (hL _ h).1 rfl
  · apply List.nodup_append.mpr
    refine ⟨hrn,List.nodup_cons.mpr ⟨fun h=>(hL _ h).2 rfl,hln⟩,?_⟩
    intro a ha b hb hab
    subst b
    rcases List.mem_cons.mp hb with hb|hb
    · exact (hR _ ha).2 hb
    · exact hcross a hb ha

 theorem splicePrefix_exterior_cycle (P : Equiv.Perm D) (x y : ℕ→D) (n l r : ℕ)
    (hd : DistinctPathMarkers x y (n+1)) (hsep : ¬P.SameCycle (x 0) (y 0))
    (hl : P^[l] (P (x n))=x 0) (hr : P^[r] (P (y 0))=y n)
    (hal : ∀i<l,∀j<n+1,P^[i] (P (x n))≠x j ∧ P^[i] (P (x n))≠y j)
    (har : ∀i<r,∀j<n+1,P^[i] (P (y 0))≠x j ∧ P^[i] (P (y 0))≠y j) :
    Function.minimalPeriod (splicePrefix P x y (n+1)) (x 0)=1+r+1+l ∧
      orbitPrefix (splicePrefix P x y (n+1))
        (Function.minimalPeriod (splicePrefix P x y (n+1)) (x 0)) (x 0)=splicedExteriorWord P x y n l r :=
  splicePrefix_exterior_period P x y n l r hd hl hr hal har
    (splicedExteriorWord_nodup P x y n l r hd hsep hl hr hal har)

section TwoInputs
variable {A B : Type} [Fintype A] [Fintype B]

 def boundaryPathSplice (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (t : ℕ) : Equiv.Perm (A⊕B) :=
  splicePrefix (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) t

 theorem sum_path_markers (x : ℕ→A) (y : ℕ→B) (t : ℕ)
    (hx : ∀i<t,∀j<t,x i=x j→i=j) (hy : ∀i<t,∀j<t,y i=y j→i=j) :
    DistinctPathMarkers (Sum.inl ∘ x) (Sum.inr ∘ y) t := by
  refine ⟨?_,?_,?_⟩
  · intro i hi j hj he
    exact hx i hi j hj (Sum.inl.inj he)
  · intro i hi j hj he
    exact hy i hi j hj (Sum.inr.inj he)
  · intro i hi j hj
    exact Sum.inl_ne_inr

 theorem boundaryPathSplice_count (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (hx : ∀i<n,P (x i)=x (i+1)) (hy : ∀i<n,Q (y (i+1))=y i) :
    count (boundaryPathSplice P Q x y (n+1))+1=count P+count Q+n := by
  have h:=count_splicePrefix (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) n
    (sum_path_markers x y (n+1) hxi hyi) (not_sameCycle_sum_cross P Q (x 0) (y 0))
    (fun i hi=>congrArg Sum.inl (hx i hi)) (fun i hi=>congrArg Sum.inr (hy i hi))
  simpa only [count_sumCongr] using h

 theorem boundaryPathSplice_digon (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (hx : ∀i<n,P (x i)=x (i+1)) (hy : ∀i<n,Q (y (i+1))=y i)
    (i : ℕ) (hi : i<n) :
    boundaryPathSplice P Q x y (n+1) (.inl (x (i+1)))=.inr (y i) ∧
      boundaryPathSplice P Q x y (n+1) (.inr (y i))=.inl (x (i+1)) :=
  splicePrefix_digon (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) n
    (sum_path_markers x y (n+1) hxi hyi)
    (fun j hj=>congrArg Sum.inl (hx j hj)) (fun j hj=>congrArg Sum.inr (hy j hj)) i hi

/-- Each input has connected Euler characteristic two. Identifying all n+1
boundary vertices and retaining both edge copies preserves that identity. -/
theorem boundaryPathSplice_euler (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (hx : ∀i<n,P (x i)=x (i+1)) (hy : ∀i<n,Q (y (i+1))=y i)
    (v₁ e₁ v₂ e₂ v e : ℕ) (h₁ : v₁+count P=e₁+2) (h₂ : v₂+count Q=e₂+2)
    (hv : v+(n+1)=v₁+v₂) (he : e=e₁+e₂) :
    v+count (boundaryPathSplice P Q x y (n+1))=e+2 := by
  have hh:=boundaryPathSplice_count P Q x y n hxi hyi hx hy
  omega

end TwoInputs
end PlanarHom.FinitePermutationCycles
