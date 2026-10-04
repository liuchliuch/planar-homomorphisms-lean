import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-! NEW exact expansion of a finite permutation cycle into first-return blocks. -/
namespace PlanarHom.FinitePermutationReturnWords

variable {A : Type*}

def orbitPrefix (P : A → A) (n : ℕ) (a : A) : List A :=
  (List.range n).map (fun i => P^[i] a)

@[simp] theorem orbitPrefix_length (P : A → A) (n : ℕ) (a : A) :
    (orbitPrefix P n a).length=n := by simp [orbitPrefix]

@[simp] theorem mem_orbitPrefix (P : A → A) (n : ℕ) (a b : A) :
    b ∈ orbitPrefix P n a ↔ ∃ i, i < n ∧ P^[i] a=b := by simp [orbitPrefix]

theorem orbitPrefix_add (P : A → A) (n m : ℕ) (a : A) :
    orbitPrefix P (n+m) a = orbitPrefix P n a ++ orbitPrefix P m (P^[n] a) := by
  simp only [orbitPrefix,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  change P^[n+i] a=P^[i] (P^[n] a)
  rw [Nat.add_comm,Function.iterate_add_apply]

theorem orbitPrefix_nodup (P : A → A) (a : A) {n : ℕ}
    (hn : n≤Function.minimalPeriod P a) : (orbitPrefix P n a).Nodup := by
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi j hj he
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (lt_of_lt_of_le (List.mem_range.mp hi) hn)
    (lt_of_lt_of_le (List.mem_range.mp hj) hn)).mp he

theorem orbitPrefix_disjoint (P : Equiv.Perm A) (q : A → Prop) (L : A → ℕ)
    (hfirst : ∀ a, q a → ∀ i, 0 < i → i < L a → ¬q (P^[i] a))
    {a b : A} (ha : q a) (hb : q b) (hne : a≠b) :
    List.Disjoint (orbitPrefix P (L a) a) (orbitPrefix P (L b) b) := by
  intro x hx hy
  obtain ⟨i,hi,he⟩ := (mem_orbitPrefix P _ _ _).mp hx
  obtain ⟨j,hj,hf⟩ := (mem_orbitPrefix P _ _ _).mp hy
  have hh : P^[i] a=P^[j] b := he.trans hf.symm
  rcases le_total i j with hij | hji
  · have hab : a=P^[j-i] b := by
      apply P.injective.iterate i
      rw [←Function.iterate_add_apply,Nat.add_sub_of_le hij]
      exact hh
    by_cases heq : i=j
    · apply hne
      simpa only [heq,Nat.sub_self,Function.iterate_zero_apply] using hab
    · exact hfirst b hb (j-i) (by omega) (by omega) (hab ▸ ha)
  · have hba : b=P^[i-j] a := by
      apply P.injective.iterate j
      rw [←Function.iterate_add_apply,Nat.add_sub_of_le hji]
      exact hh.symm
    by_cases heq : j=i
    · apply hne
      simpa only [heq,Nat.sub_self,Function.iterate_zero_apply] using hba.symm
    · exact hfirst a ha (i-j) (by omega) (by omega) (hba ▸ hb)

def returnTime (Q : A → A) (L : A → ℕ) (a : A) : ℕ → ℕ
  | 0 => 0
  | n+1 => returnTime Q L a n + L (Q^[n] a)

theorem return_expansion (P Q : A → A) (q : A → Prop) (L : A → ℕ)
    (hQ : ∀ a, q a → q (Q a)) (hend : ∀ a, q a → P^[L a] a=Q a)
    (a : A) (ha : q a) (n : ℕ) :
    P^[returnTime Q L a n] a=Q^[n] a ∧
      (orbitPrefix Q n a).flatMap (fun b => orbitPrefix P (L b) b)=
        orbitPrefix P (returnTime Q L a n) a := by
  have hiter : ∀ i, q (Q^[i] a) := by
    intro i
    induction i with
    | zero => exact ha
    | succ i ih => rw [Function.iterate_succ_apply']; exact hQ _ ih
  induction n with
  | zero => simp [returnTime,orbitPrefix]
  | succ n ih =>
      constructor
      · rw [returnTime,Nat.add_comm,Function.iterate_add_apply,ih.1,hend _ (hiter n),
          Function.iterate_succ_apply']
      · change ((List.range (n+1)).map (fun i => Q^[i] a)).flatMap _ = _
        rw [List.range_succ,List.map_append,List.flatMap_append]
        simp only [List.map_singleton,List.flatMap_singleton]
        rw [show ((List.range n).map (fun i => Q^[i] a)).flatMap
            (fun b => orbitPrefix P (L b) b)=orbitPrefix P (returnTime Q L a n) a from ih.2]
        rw [returnTime,orbitPrefix_add,ih.1]

theorem period_eq_of_prefix_nodup [Finite A] (P : Equiv.Perm A) (a : A) (n : ℕ)
    (hn : 0 < n) (hend : P^[n] a=a) (hnd : (orbitPrefix P n a).Nodup) :
    Function.minimalPeriod P a=n := by
  apply le_antisymm ((show Function.IsPeriodicPt P n a from hend).minimalPeriod_le hn)
  by_contra hh
  have hp : Function.minimalPeriod P a<n := by omega
  have hp0 := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
  have hz : 0 < (orbitPrefix P n a).length := by simpa using hn
  have hi : Function.minimalPeriod P a < (orbitPrefix P n a).length := by simpa using hp
  have he : (orbitPrefix P n a)[0]=(orbitPrefix P n a)[Function.minimalPeriod P a] := by
    simp only [orbitPrefix,List.getElem_map,List.getElem_range,Function.iterate_zero_apply]
    exact (Function.isPeriodicPt_minimalPeriod P a).symm
  have := hnd.getElem_inj_iff.mp he
  omega

theorem cycle_return_expansion [Finite A] (P Q : Equiv.Perm A) (q : A → Prop)
    (L : A → ℕ) (hQ : ∀ a, q a → q (Q a))
    (hpos : ∀ a, q a → 0 < L a)
    (hle : ∀ a, q a → L a≤Function.minimalPeriod P a)
    (hend : ∀ a, q a → P^[L a] a=Q a)
    (hfirst : ∀ a, q a → ∀ i, 0 < i → i < L a → ¬q (P^[i] a))
    (a : A) (ha : q a) :
    (orbitPrefix Q (Function.minimalPeriod Q a) a).flatMap
        (fun b => orbitPrefix P (L b) b)=orbitPrefix P (Function.minimalPeriod P a) a := by
  let N := Function.minimalPeriod Q a
  let T := returnTime Q L a N
  have hN : 0 < N := Function.minimalPeriod_pos_of_mem_periodicPts (Q.injective.mem_periodicPts a)
  have hiter : ∀ i, q (Q^[i] a) := by
    intro i
    induction i with
    | zero => exact ha
    | succ i ih => rw [Function.iterate_succ_apply']; exact hQ _ ih
  have hmem : ∀ b ∈ orbitPrefix Q N a, q b := by
    intro b hb
    obtain ⟨i,_,rfl⟩ := (mem_orbitPrefix Q _ _ _).mp hb
    exact hiter i
  have hT : 0 < T := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    dsimp only [T]
    rw [hn,returnTime]
    have := hpos _ (hiter n)
    omega
  obtain ⟨hendT,hexp⟩ := return_expansion P Q q L hQ hend a ha N
  have hperiod : Function.IsPeriodicPt P T a := by
    exact hendT.trans (Function.isPeriodicPt_minimalPeriod Q a)
  have hnd : (orbitPrefix P T a).Nodup := by
    rw [←hexp]
    apply List.nodup_flatMap.mpr
    refine ⟨fun b hb => orbitPrefix_nodup P b (hle b (hmem b hb)),?_⟩
    exact (orbitPrefix_nodup Q a (le_refl N)).imp_of_mem
      (fun {b c} hb hc hbc => orbitPrefix_disjoint P q L hfirst (hmem b hb) (hmem c hc) hbc)
  have hleT : T≤Function.minimalPeriod P a := by
    by_contra hn
    have hp : Function.minimalPeriod P a<T := by omega
    have hp0 := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
    have hz : 0 < (orbitPrefix P T a).length := by simpa using hT
    have hi : Function.minimalPeriod P a < (orbitPrefix P T a).length := by simpa using hp
    have he : (orbitPrefix P T a)[0]=(orbitPrefix P T a)[Function.minimalPeriod P a] := by
      simp only [orbitPrefix,List.getElem_map,List.getElem_range,Function.iterate_zero_apply]
      exact (Function.isPeriodicPt_minimalPeriod P a).symm
    have := hnd.getElem_inj_iff.mp he
    omega
  have hTeq : T=Function.minimalPeriod P a := le_antisymm hleT (hperiod.minimalPeriod_le hT)
  simpa only [←hTeq] using hexp

theorem orbitPrefix_cycle_rotate (P : A → A) (a : A) (k : ℕ) :
    orbitPrefix P (Function.minimalPeriod P a) (P^[k] a)=
      (orbitPrefix P (Function.minimalPeriod P a) a).rotate k := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [List.getElem_rotate]
  simp only [orbitPrefix,List.getElem_map,List.getElem_range,List.length_map,List.length_range]
  rw [Function.iterate_mod_minimalPeriod_eq,Function.iterate_add_apply]

theorem filter_rotate_eq_of_drop_eq_nil (xs : List A) (keep : A → Bool) (k : ℕ)
    (hk : k≤xs.length) (hdrop : (xs.drop k).filter keep=[]) :
    (xs.rotate k).filter keep=xs.filter keep := by
  rw [List.rotate_eq_drop_append_take hk,List.filter_append,hdrop,List.nil_append]
  conv_rhs => rw [←List.take_append_drop k xs,List.filter_append,hdrop,List.append_nil]

end PlanarHom.FinitePermutationReturnWords
