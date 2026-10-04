import PlanarHom.RankFourStructuralTransport
import PlanarHom.RankFourSingleBlock

/-! Four colors force every genuine nontrivial direct sum to have sizes 1+3
or 2+2, after interchanging the summands. Both displayed blocks retain their
literal structural tractability certificates. -/
noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures

/-- An actual nonempty direct sum, using its subset chart on the original colors. -/
def SplitClass (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃p : Fin 4→Prop,
    ((Nat.card {i//p i}=1 ∧ Nat.card {i//¬p i}=3) ∨
     (Nat.card {i//p i}=2 ∧ Nat.card {i//¬p i}=2)) ∧
    (∀i j,p i→¬p j→M i j=0) ∧ (∀i j,¬p i→p j→M i j=0) ∧
    NonnegativeClass (fun i j:{c//p c}=>M i.val j.val) ∧
    NonnegativeClass (fun i j:{c//¬p c}=>M i.val j.val)

theorem split_of_partition (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀i j,M i j=M j i) (p : Fin 4→Prop)
    (hp : Nonempty {i//p i}) (hn : Nonempty {i//¬p i})
    (hz : ∀i j,p i→¬p j→M i j=0)
    (ha : NonnegativeClass (fun i j:{c//p c}=>M i.val j.val))
    (hb : NonnegativeClass (fun i j:{c//¬p c}=>M i.val j.val)) : SplitClass M := by
  have hcp : 0<Nat.card {i//p i} := by simpa only [Nat.card_eq_fintype_card] using Fintype.card_pos_iff.mpr hp
  have hcn : 0<Nat.card {i//¬p i} := by simpa only [Nat.card_eq_fintype_card] using Fintype.card_pos_iff.mpr hn
  have hc := Nat.card_congr (Equiv.sumCompl p)
  simp only [Nat.card_sum,Nat.card_fin] at hc
  have hzr : ∀i j,¬p i→p j→M i j=0 := by
    intro i j hi hj; rw [hs]; exact hz j i hj hi
  by_cases hsmall : Nat.card {i//p i}≤2
  · refine ⟨p,?_,hz,hzr,ha,hb⟩
    omega
  · let e : {i//¬¬p i}≃{i//p i} := Equiv.subtypeEquivRight (fun _=>not_not)
    have he := Nat.card_congr e
    refine ⟨fun i=>¬p i,?_,?_,?_,hb,ha.equiv e⟩
    · change (Nat.card {i//¬p i}=1 ∧ Nat.card {i//¬¬p i}=3) ∨
        (Nat.card {i//¬p i}=2 ∧ Nat.card {i//¬¬p i}=2)
      change Nat.card {i//¬¬p i}=Nat.card {i//p i} at he
      omega
    · intro i j hi hj; exact hzr i j hi (not_not.mp hj)
    · intro i j hi hj; exact hz i j (not_not.mp hi) hj

theorem nonnegativeClass_split_or_allowed {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : NonnegativeClass M) : SplitClass M ∨ AllowedBlock M := by
  have hsym := h.symmetric
  obtain ⟨t,b,hb,hz,ha⟩:=h
  have ht : 0<t := lt_of_le_of_lt (Nat.zero_le _) (b 0).isLt
  by_cases ht1 : t=1
  · subst t
    right
    let e : Fin 4≃{c//b c=0} := {
      toFun := fun c=>⟨c,Fin.eq_zero _⟩
      invFun := Subtype.val
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
    exact (ha 0).equiv e
  · have ht2 : 1<t := by omega
    let r : Fin t := ⟨0,ht⟩
    let s : Fin t := ⟨1,ht2⟩
    have hsr : s≠r := by intro hh; have:=congrArg Fin.val hh; simp [s,r] at this
    have hp : Nonempty {i//b i=r} := by
      obtain ⟨i,hi⟩:=hb r
      exact ⟨⟨i,hi⟩⟩
    have hn : Nonempty {i//b i≠r} := by
      obtain ⟨i,hi⟩:=hb s
      exact ⟨⟨i,by simpa [hi] using hsr⟩⟩
    left
    apply split_of_partition M hsym (fun i=>b i=r) hp hn
    · intro i j hi hj; exact hz i j (by intro he; exact hj (he.symm.trans hi))
    · exact (ha r).nonnegativeClass
    · exact complement_fiber_class M b hb hz ha r

theorem nonnegativeClass_rank_four_forms {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hr : M.rank=4) (h : NonnegativeClass M) : SplitClass M ∨ SingleTensor M := by
  rcases nonnegativeClass_split_or_allowed h with hs|ha
  · exact .inl hs
  · exact .inr (allowedBlock_singleTensor (Fintype.card_fin 4) hr ha)

end PlanarHom.RankFour
