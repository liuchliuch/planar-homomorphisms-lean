import PlanarHom.FinitePermutationFiberCount

/-! A finite cycle-label certificate checked by local successor equations.
Decreasing ranks prove that every dart reaches its own displayed root. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D L : Type} [Fintype D] [Fintype L]

 structure LabelCertificate (P : Equiv.Perm D) (L : Type) where
  label : D → L
  root : L → D
  rank : D → ℕ
  root_label : ∀l,label (root l)=l
  step_label : ∀d,label (P d)=label d
  zero_root : ∀d,rank d=0 → d=root (label d)
  step_rank : ∀d,0<rank d → rank (P d)+1=rank d

 theorem LabelCertificate.reaches_root {P : Equiv.Perm D} (C : LabelCertificate P L) (d : D) :
    P.SameCycle d (C.root (C.label d)) := by
  suffices ∀n,∀d,C.rank d=n → P.SameCycle d (C.root (C.label d)) from this _ d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hd
    by_cases hz : C.rank d=0
    · have he := C.zero_root d hz
      rw [he,C.root_label]
    · have hpos := Nat.pos_of_ne_zero hz
      have hr := C.step_rank d hpos
      have hh := ih (C.rank (P d)) (by omega) (P d) rfl
      rw [C.step_label] at hh
      exact Equiv.Perm.SameCycle.rfl.apply_right.trans hh

 theorem LabelCertificate.sameCycle_iff {P : Equiv.Perm D} (C : LabelCertificate P L) (a b : D) :
    P.SameCycle a b ↔ C.label a=C.label b := by
  constructor
  · exact label_sameCycle P C.label C.step_label
  · intro h
    have ha := C.reaches_root a
    have hb := C.reaches_root b
    rw [h] at ha
    exact ha.trans hb.symm

 def LabelCertificate.cycleEquiv {P : Equiv.Perm D} (C : LabelCertificate P L) :
    Quotient (Equiv.Perm.SameCycle.setoid P) ≃ L where
  toFun := Quotient.lift C.label (fun a b h => (C.sameCycle_iff a b).mp h)
  invFun l := Quotient.mk _ (C.root l)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h d => exact Quotient.sound (C.reaches_root d).symm
  right_inv l := C.root_label l

 theorem LabelCertificate.count {P : Equiv.Perm D} (C : LabelCertificate P L) :
    count P=Fintype.card L :=
  (Nat.card_congr C.cycleEquiv).trans Nat.card_eq_fintype_card
end PlanarHom.FinitePermutationCycles
