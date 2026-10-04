import PlanarHom.FinitePermutationMarkerBalance
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual recursive deletion of finitely many inactive darts, with the exact
rotation/face cycle balance. The rotation may have any number of vertex rows. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {A : Type} [Fintype A]

 def markerOptionEquiv (n : ℕ) : A ⊕ Fin (n+1) ≃ Option (A ⊕ Fin n) where
  toFun
    | .inl a => some (.inl a)
    | .inr j => Fin.cases none (fun i => some (.inr i)) j
  invFun
    | none => .inr 0
    | some (.inl a) => .inl a
    | some (.inr j) => .inr j.succ
  left_inv x := by
    rcases x with a | j
    · rfl
    · refine Fin.cases rfl (fun j => rfl) j
  right_inv x := by rcases x with _ | (a | j) <;> rfl

 def eraseFinMarkers : {n : ℕ} → Equiv.Perm (A ⊕ Fin n) → Equiv.Perm A
  | 0,R => (Equiv.sumEmpty A (Fin 0)).permCongr R
  | n+1,R => eraseFinMarkers (Equiv.removeNone ((markerOptionEquiv n).permCongr R))

 theorem permCongr_mul {B : Type} (e : A≃B) (P Q : Equiv.Perm A) :
    e.permCongr (P*Q)=e.permCongr P*e.permCongr Q := by
  apply Equiv.ext
  intro b
  simp only [Equiv.permCongr_apply,Equiv.Perm.mul_apply,Equiv.symm_apply_apply]

 theorem markerOption_fixed (n : ℕ) (I : Equiv.Perm A) :
    (markerOptionEquiv (A:=A) n).permCongr (Equiv.sumCongr I (Equiv.refl (Fin (n+1))))=
      (Equiv.sumCongr I (Equiv.refl (Fin n))).optionCongr := by
  apply Equiv.ext
  intro b
  rcases b with _ | (a | j) <;> rfl

 theorem markerZero_fixed (I : Equiv.Perm A) :
    (Equiv.sumEmpty A (Fin 0)).permCongr (Equiv.sumCongr I (Equiv.refl (Fin 0)))=I := by
  apply Equiv.ext
  intro a
  rfl

/-- Deleting fixed edge-flip markers preserves Euler defect exactly. -/
 theorem eraseFinMarkers_count_balance (n : ℕ) (R : Equiv.Perm (A ⊕ Fin n))
    (I : Equiv.Perm A) :
    count (R*Equiv.sumCongr I (Equiv.refl (Fin n)))+count (eraseFinMarkers R)=
      count (eraseFinMarkers R*I)+count R := by
  induction n with
  | zero =>
      have hf := count_permCongr (R*Equiv.sumCongr I (Equiv.refl (Fin 0)))
        (Equiv.sumEmpty A (Fin 0))
      rw [permCongr_mul,markerZero_fixed] at hf
      have hr := count_permCongr R (Equiv.sumEmpty A (Fin 0))
      change count (eraseFinMarkers R*I)=_ at hf
      change count (eraseFinMarkers R)=_ at hr
      omega
  | succ n ih =>
      let S := (markerOptionEquiv (A:=A) n).permCongr R
      let J := Equiv.sumCongr I (Equiv.refl (Fin n))
      have hstep := removeNone_count_balance S J
      have hind := ih (Equiv.removeNone S)
      have hr : count S=count R := count_permCongr R (markerOptionEquiv n)
      have hf : count (S*J.optionCongr)=
          count (R*Equiv.sumCongr I (Equiv.refl (Fin (n+1)))) := by
        have hh := count_permCongr (R*Equiv.sumCongr I (Equiv.refl (Fin (n+1))))
          (markerOptionEquiv (A:=A) n)
        rw [permCongr_mul,markerOption_fixed] at hh
        exact hh
      change count (R*Equiv.sumCongr I (Equiv.refl (Fin (n+1))))+
        count (eraseFinMarkers (Equiv.removeNone S))=
        count (eraseFinMarkers (Equiv.removeNone S)*I)+count R
      rw [hf,hr] at hstep
      dsimp [J] at hstep
      omega

/-- The corresponding face correction when complete vertex rows have already
been counted. This includes inactive-only vertices and an empty visible graph. -/
 theorem eraseFinMarkers_face_count (n : ℕ) (R : Equiv.Perm (A ⊕ Fin n))
    (I : Equiv.Perm A) (visibleVertices inactiveVertices : ℕ)
    (hfull : count R=visibleVertices+inactiveVertices)
    (hretained : count (eraseFinMarkers R)=visibleVertices) :
    count (R*Equiv.sumCongr I (Equiv.refl (Fin n)))=
      count (eraseFinMarkers R*I)+inactiveVertices := by
  have h := eraseFinMarkers_count_balance n R I
  omega
end PlanarHom.FinitePermutationCycles
