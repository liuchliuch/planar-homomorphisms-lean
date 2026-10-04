import PlanarHom.IndexedRotationCertificate
import PlanarHom.PottsOccurrenceReversal

/-! The numeric face certificate is the actual full-boundary Euler identity
for the literal occurrence graph, not a disconnected table of cycle counts. -/
noncomputable section
open Classical
namespace PlanarHom.IndexedRotationCertificate
open MultiGraph FinitePermutationCycles RadialPotts.Assembly PlanarityLRRealization

 theorem face_step {m : ℕ} (P : Equiv.Perm (Fin (2*m))) (d : Medial.Dart (Fin m)) :
    dartIndexEquiv m ((rotation P*reversePerm (Fin m)) d)=P (dartIndexEquiv m d) := by
  have h : flip m (dartIndexEquiv m (reversePerm (Fin m) d))=dartIndexEquiv m d := by
    rcases d with ⟨e,b⟩
    change flip m (dartIndexEquiv m (e,!b))=dartIndexEquiv m (e,b)
    rw [flip_index]
    cases b <;> rfl
  change dartIndexEquiv m (rotation P (reversePerm (Fin m) d))=_
  simp only [rotation,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
    Equiv.Perm.mul_apply]
  rw [h]

 theorem face_count {m : ℕ} (P : Equiv.Perm (Fin (2*m))) :
    count (subsetBoundary (rotation P) Finset.univ)=count P := by
  rw [full_boundary_count_face]
  exact count_of_step _ _ (dartIndexEquiv m) (face_step P)

 theorem ConnectivityCertificate.componentCount {n m : ℕ} {G : MultiGraph (Fin n) (Fin m)}
    (C : ConnectivityCertificate G) : G.componentCount Finset.univ=1 := by
  letI : Subsingleton (G.Components Finset.univ) := ⟨by
    intro x y
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b => exact Quotient.sound (C.connected a b)⟩
  letI : Nonempty (G.Components Finset.univ) := ⟨Quotient.mk _ C.root⟩
  exact (Nat.card_eq_fintype_card (α:=G.Components Finset.univ)).symm.trans Nat.card_unique

 theorem euler {n m : ℕ} (host : Fin (2*m) → Fin n)
    (P : Equiv.Perm (Fin (2*m))) (C : ConnectivityCertificate (graph host))
    (he : n+count P=m+2) :
    Fintype.card (Fin n)+count (subsetBoundary (rotation P) Finset.univ)=
      Fintype.card (Fin m)+2*(graph host).componentCount Finset.univ := by
  rw [face_count,C.componentCount,Fintype.card_fin,Fintype.card_fin]
  omega
end PlanarHom.IndexedRotationCertificate
