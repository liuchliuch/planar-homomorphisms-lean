import PlanarHom.FinitePermutationCycleInsertion
import PlanarHom.FinitePermutationFixedCycle
import PlanarHom.PlanarityLRRealizationRotationSystem

/-! NEW exact permutation identity for inserting one adjacent reverse dart pair. -/
noncomputable section
namespace PlanarHom.NoncrossingBouquet
open FinitePermutationCycles
variable {A : Type*} [DecidableEq A]

abbrev TwoFresh (A : Type*) := (A⊕Unit)⊕Unit

def oldDart (a : A) : TwoFresh A := .inl (.inl a)
def firstDart : TwoFresh A := .inl (.inr ())
def secondDart : TwoFresh A := .inr ()

def pairReverse (R : Equiv.Perm A) : Equiv.Perm (TwoFresh A) :=
  (Equiv.sumCongr (Equiv.sumCongr R (Equiv.refl Unit)) (Equiv.refl Unit)).trans
    (Equiv.swap firstDart secondDart)

@[simp] theorem pairReverse_old (R : Equiv.Perm A) (a : A) : pairReverse R (oldDart a)=oldDart (R a) := by
  simp [pairReverse,oldDart,firstDart,secondDart,Equiv.swap_apply_of_ne_of_ne]
@[simp] theorem pairReverse_first (R : Equiv.Perm A) : pairReverse R firstDart=secondDart := by
  simp [pairReverse,firstDart,secondDart]
@[simp] theorem pairReverse_second (R : Equiv.Perm A) : pairReverse R secondDart=firstDart := by
  simp [pairReverse,firstDart,secondDart]

def pairWord (word : List A) : List (TwoFresh A) := firstDart::secondDart::word.map oldDart

theorem oldDart_injective : Function.Injective (oldDart (A:=A)) := by
  intro a b h
  exact Sum.inl.inj (Sum.inl.inj h)

theorem pairWord_nodup (word : List A) (hn : word.Nodup) : (pairWord word).Nodup := by
  simp [pairWord,firstDart,secondDart,oldDart,List.nodup_map_iff_inj_on,hn]

theorem pairWord_face_eq (R : Equiv.Perm A) (c : A) (cs : List A)
    (hn : (c::cs).Nodup) (hfull : ∀a,a∈c::cs) :
    (pairWord (c::cs)).formPerm * pairReverse R=
      addFixed (insertAfter ((c::cs).formPerm * R) (((c::cs).formPerm * R)⁻¹ c)) := by
  let Q := (c::cs).formPerm * R
  let mark := Q⁻¹ c
  have hm : Q mark=c := Q.apply_symm_apply c
  have hmap (x : A) : ((c::cs).map oldDart).formPerm (oldDart (R x))=oldDart (Q x) :=
    (PlanarityLRRealization.map_formPerm_apply oldDart oldDart_injective (c::cs) hn (hfull (R x)))
  apply Equiv.ext
  intro x
  rcases x with (x | u) | u
  · change (pairWord (c::cs)).formPerm (pairReverse R (oldDart x))=_
    rw [pairReverse_old]
    change (firstDart::secondDart::oldDart c::cs.map oldDart).formPerm (oldDart (R x))=_
    rw [List.formPerm_cons_cons,List.formPerm_cons_cons,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply]
    rw [show (oldDart c::cs.map oldDart).formPerm (oldDart (R x))=oldDart (Q x) from hmap x]
    change Equiv.swap firstDart secondDart (Equiv.swap secondDart (oldDart c) (oldDart (Q x)))=
      Sum.inl (insertAfter Q mark (.inl x))
    by_cases hx : x=mark
    · subst x
      rw [hm,insertAfter_mark]
      simp [oldDart,firstDart,secondDart]
    · have hxc : Q x≠c := by intro he; exact hx (Q.injective (he.trans hm.symm))
      rw [insertAfter_old Q mark x hx]
      simp [oldDart,firstDart,secondDart,Equiv.swap_apply_of_ne_of_ne,hxc]
  · cases u
    change (pairWord (c::cs)).formPerm (pairReverse R firstDart)=Sum.inl (insertAfter Q mark (.inr ()))
    rw [pairReverse_first,insertAfter_new,hm]
    change (firstDart::secondDart::oldDart c::cs.map oldDart).formPerm secondDart=oldDart c
    rw [List.formPerm_cons_cons,Equiv.Perm.mul_apply,
      List.formPerm_apply_head secondDart (oldDart c) (cs.map oldDart) (List.nodup_cons.mp (pairWord_nodup _ hn)).2]
    simp [oldDart,firstDart,secondDart,Equiv.swap_apply_of_ne_of_ne]
  · cases u
    change (pairWord (c::cs)).formPerm (pairReverse R secondDart)=secondDart
    rw [pairReverse_second]
    exact List.formPerm_apply_head firstDart secondDart _ (pairWord_nodup _ hn)

theorem count_pairWord [Finite A] (R : Equiv.Perm A) (c : A) (cs : List A)
    (hn : (c::cs).Nodup) (hfull : ∀a,a∈c::cs) :
    count ((pairWord (c::cs)).formPerm * pairReverse R)=count ((c::cs).formPerm * R)+1 := by
  rw [pairWord_face_eq R c cs hn hfull,count_addFixed,count_insertAfter]

end PlanarHom.NoncrossingBouquet
