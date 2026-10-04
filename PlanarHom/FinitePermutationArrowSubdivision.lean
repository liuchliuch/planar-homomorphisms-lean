import PlanarHom.FinitePermutationCycleProducts
import PlanarHom.FinitePermutationCycleTransport

/-! NEW literal cycle-count identities for finite ribbon gadget insertion.
Subdividing every permutation arrow preserves all cycles, including fixed ones. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {A B : Type*} [Fintype A] [Fintype B]

 theorem sameCycle_map_of_step (P : Equiv.Perm A) (Q : Equiv.Perm B) (f : A→B)
    (hs : ∀a,Q.SameCycle (f a) (f (P a))) {a b : A} (h : P.SameCycle a b) :
    Q.SameCycle (f a) (f b) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi : ∀n,Q.SameCycle (f a) (f (P^[n] a)) := by
    intro n
    induction n with
    | zero => exact .rfl
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (hs _)
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using hi n

 theorem count_inv (P : Equiv.Perm A) : count P⁻¹=count P :=
  count_congr _ _ (Equiv.refl _) (fun _ _=>Equiv.Perm.sameCycle_inv)

 private theorem sum_iterate_left (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (a : A) :
    (Equiv.sumCongr P Q)^[n] (.inl a)=.inl (P^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

 private theorem sum_iterate_right (P : Equiv.Perm A) (Q : Equiv.Perm B) (n : ℕ) (b : B) :
    (Equiv.sumCongr P Q)^[n] (.inr b)=.inr (Q^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

 theorem sameCycle_sum_left (P : Equiv.Perm A) (Q : Equiv.Perm B) (a b : A) :
    Equiv.Perm.SameCycle (Equiv.sumCongr P Q) (.inl a) (.inl b) ↔ P.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hi := sum_iterate_left P Q n a
    rw [Equiv.Perm.iterate_eq_pow,hn] at hi
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using (Sum.inl.inj hi).symm⟩
  · exact sameCycle_map_of_step P (Equiv.sumCongr P Q) Sum.inl (fun a=>Equiv.Perm.SameCycle.rfl.apply_right)

 theorem sameCycle_sum_right (P : Equiv.Perm A) (Q : Equiv.Perm B) (a b : B) :
    Equiv.Perm.SameCycle (Equiv.sumCongr P Q) (.inr a) (.inr b) ↔ Q.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hi := sum_iterate_right P Q n a
    rw [Equiv.Perm.iterate_eq_pow,hn] at hi
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using (Sum.inr.inj hi).symm⟩
  · exact sameCycle_map_of_step Q (Equiv.sumCongr P Q) Sum.inr (fun a=>Equiv.Perm.SameCycle.rfl.apply_right)

 theorem not_sameCycle_sum_cross (P : Equiv.Perm A) (Q : Equiv.Perm B) (a : A) (b : B) :
    ¬Equiv.Perm.SameCycle (Equiv.sumCongr P Q) (.inl a) (.inr b) := by
  intro h
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi := sum_iterate_left P Q n a
  rw [Equiv.Perm.iterate_eq_pow,hn] at hi
  contradiction

 theorem count_sumCongr (P : Equiv.Perm A) (Q : Equiv.Perm B) :
    count (Equiv.sumCongr P Q)=count P+count Q := by
  let label : A⊕B→CycleClass P⊕CycleClass Q := Sum.map (classOf P) (classOf Q)
  have hsurj : Function.Surjective label := by
    intro q
    rcases q with q|q
    · induction q using Quotient.inductionOn with | h a => exact ⟨.inl a,rfl⟩
    · induction q using Quotient.inductionOn with | h b => exact ⟨.inr b,rfl⟩
  have he : ∀a b,Equiv.Perm.SameCycle (Equiv.sumCongr P Q) a b ↔ label a=label b := by
    intro a b
    rcases a with a|a <;> rcases b with b|b
    · simp only [label,Sum.map_inl,Sum.inl.injEq,sameCycle_sum_left]
      exact ⟨fun h=>Quotient.sound h,fun h=>Quotient.exact h⟩
    · simp only [label,Sum.map_inl,Sum.map_inr,Sum.inl_ne_inr,iff_false]
      exact not_sameCycle_sum_cross P Q a b
    · simp only [label,Sum.map_inl,Sum.map_inr,Sum.inr_ne_inl,iff_false]
      exact fun h=>not_sameCycle_sum_cross P Q b a h.symm
    · simp only [label,Sum.map_inr,Sum.inr.injEq,sameCycle_sum_right]
      exact ⟨fun h=>Quotient.sound h,fun h=>Quotient.exact h⟩
  rw [count_eq_card_of_label _ label hsurj he,Fintype.card_sum]
  simp [count,Nat.card_eq_fintype_card,CycleClass]

 def subdivideArrows (P : Equiv.Perm A) : Equiv.Perm (A⊕A) where
  toFun := Sum.elim Sum.inr (fun a=>Sum.inl (P a))
  invFun := Sum.elim (fun a=>Sum.inr (P.symm a)) Sum.inl
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

 theorem subdivideArrows_sameCycle (P : Equiv.Perm A) (a b : A⊕A) :
    (subdivideArrows P).SameCycle a b ↔ P.SameCycle (Sum.elim id id a) (Sum.elim id id b) := by
  let collapse : A⊕A→A := Sum.elim id id
  have hproj : ∀a,P.SameCycle (collapse a) (collapse (subdivideArrows P a)) := by
    intro a
    cases a with
    | inl a => exact .rfl
    | inr a => exact Equiv.Perm.SameCycle.rfl.apply_right
  have hstep : ∀a,(subdivideArrows P).SameCycle (.inl a) (.inl (P a)) := by
    intro a
    exact (Equiv.Perm.SameCycle.rfl.apply_right).apply_right
  have hcollapse : ∀a,(subdivideArrows P).SameCycle a (.inl (collapse a)) := by
    intro a
    cases a with
    | inl a => exact .rfl
    | inr a => exact (show (subdivideArrows P).SameCycle (.inl a) (.inr a) from Equiv.Perm.SameCycle.rfl.apply_right).symm
  constructor
  · exact sameCycle_map_of_step (subdivideArrows P) P collapse hproj
  · intro h
    exact (hcollapse a).trans ((sameCycle_map_of_step P (subdivideArrows P) Sum.inl hstep h).trans (hcollapse b).symm)

 theorem count_subdivideArrows (P : Equiv.Perm A) : count (subdivideArrows P)=count P := by
  let label : A⊕A→CycleClass P := fun a=>classOf P (Sum.elim id id a)
  have hsurj : Function.Surjective label := by
    intro q
    induction q using Quotient.inductionOn with | h a => exact ⟨.inl a,rfl⟩
  rw [count_eq_card_of_label _ label hsurj (fun a b=>(subdivideArrows_sameCycle P a b).trans ⟨fun h=>Quotient.sound h,fun h=>Quotient.exact h⟩)]
  exact Nat.card_eq_fintype_card.symm

end PlanarHom.FinitePermutationCycles
