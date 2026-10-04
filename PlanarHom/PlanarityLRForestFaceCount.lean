import PlanarHom.FinitePermutationFixedMarkers
import PlanarHom.NoncrossingBouquetFaceCount
import PlanarHom.FinitePermutationReturnWords
import PlanarHom.PlanarityLRContourPermutation

/-! NEW direct face counting from a single full forest contour. Contracted tree
darts are proved to be fixed markers; no geometric face/Euler premise is used. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn FinitePermutationReturnWords FinitePermutationCycles

 def partitionDartEquiv {E : Type*} (selected : E → Bool) :
    Dart E ≃ Dart {e // selected e=false} ⊕ Dart {e // selected e=true} where
  toFun a := if h : selected a.1=true then .inr (⟨a.1,h⟩,a.2)
    else .inl (⟨a.1,Bool.eq_false_iff.mpr h⟩,a.2)
  invFun
    | .inl a => (a.1.val,a.2)
    | .inr a => (a.1.val,a.2)
  left_inv a := by dsimp only; split_ifs <;> rfl
  right_inv a := by
    rcases a with ⟨⟨e,he⟩,b⟩ | ⟨⟨e,he⟩,b⟩
    · simp only [he,Bool.false_eq_true,↓reduceDIte]
    · simp only [he,↓reduceDIte]

 theorem partitionDartEquiv_reverseVisible {E : Type*} (selected : E → Bool) (a : Dart E) :
    partitionDartEquiv selected (partialReverse E (fun e => !(selected e)) a)=
      (Equiv.sumCongr (reversePerm {e // selected e=false}) (Equiv.refl (Dart {e // selected e=true})))
        (partitionDartEquiv selected a) := by
  rcases a with ⟨e,b⟩
  cases he : selected e <;> simp [partialReverse,partitionDartEquiv,reversePerm,he]

 theorem face_eq_contour_mul_visible {E : Type*} (R : Equiv.Perm (Dart E)) (selected : E → Bool) :
    (reversePerm E).trans R=
      ((partialReverse E selected).trans R) * partialReverse E (fun e => !(selected e)) := by
  apply Equiv.ext
  intro a
  rcases a with ⟨e,b⟩
  cases he : selected e <;> simp [partialReverse,reversePerm,he]

 theorem mem_fullContourWord {A : Type*} [Finite A] (C : Equiv.Perm A) (a x : A)
    (hsingle : ∀x,C.SameCycle a x) : x∈orbitPrefix C (Function.minimalPeriod C a) a := by
  obtain ⟨n,hn⟩ := (hsingle x).exists_nat_pow_eq
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (C.injective.mem_periodicPts a)
  apply (mem_orbitPrefix C _ _ _).mpr
  refine ⟨n%Function.minimalPeriod C a,Nat.mod_lt _ hp,?_⟩
  rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
  exact hn

 theorem formPerm_fullContourWord {A : Type*} [Finite A] [DecidableEq A]
    (C : Equiv.Perm A) (a : A) (hsingle : ∀x,C.SameCycle a x) :
    (orbitPrefix C (Function.minimalPeriod C a) a).formPerm=C := by
  have hn := orbitPrefix_nodup C a (le_refl (Function.minimalPeriod C a))
  ext x
  obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp (mem_fullContourWord C a x hsingle)
  rw [←hix,List.formPerm_apply_getElem _ hn i hi]
  simp only [orbitPrefix,List.getElem_map,List.getElem_range,List.length_map,List.length_range]
  rw [Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']

 theorem count_singleCycle {A : Type*} (C : Equiv.Perm A) (a : A)
    (hsingle : ∀x,C.SameCycle a x) : count C=1 := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid C) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => Quotient.mk _ a
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        exact Quotient.sound (hsingle x)
      right_inv := fun u => Subsingleton.elim _ _ }
  exact (Nat.card_congr e).trans (by simp)

 def visibleContourWord {E : Type*} (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E) :
    List (Dart {e // selected e=false}) :=
  visibleWord ((orbitPrefix ((partialReverse E selected).trans R)
    (Function.minimalPeriod ((partialReverse E selected).trans R) a) a).map (partitionDartEquiv selected))

 theorem visibleContourWord_nodup {E : Type*} (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E) :
    (visibleContourWord R selected a).Nodup :=
  visibleWord_nodup ((orbitPrefix_nodup _ a (le_refl _)).map (partitionDartEquiv selected).injective)

 theorem visibleContourWord_full {E : Type*} [Finite E]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x) :
    ∀x,x∈visibleContourWord R selected a := by
  apply visibleWord_full
  intro x
  exact List.mem_map.mpr ⟨(partitionDartEquiv selected).symm x,
    mem_fullContourWord _ a _ hsingle,Equiv.apply_symm_apply _ _⟩

 theorem count_faces_eq_bouquet {E : Type*} [Finite E] [DecidableEq E]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x)
    [Nonempty {e // selected e=false}] :
    count ((reversePerm E).trans R)=
      count ((visibleContourWord R selected a).formPerm * reversePerm {e // selected e=false}) := by
  let C := (partialReverse E selected).trans R
  let xs := orbitPrefix C (Function.minimalPeriod C a) a
  have hn : xs.Nodup := orbitPrefix_nodup C a (le_refl _)
  have hfull : ∀x,x∈xs := fun x => mem_fullContourWord C a x hsingle
  have ht := count_mapped_word (partialReverse E (fun e => !(selected e)))
    (Equiv.sumCongr (reversePerm {e // selected e=false}) (Equiv.refl (Dart {e // selected e=true})))
    (partitionDartEquiv selected) (partitionDartEquiv_reverseVisible selected) xs hn hfull
  have hmapfull : ∀x,x∈xs.map (partitionDartEquiv selected) := by
    intro x
    exact List.mem_map.mpr ⟨(partitionDartEquiv selected).symm x,hfull _,Equiv.apply_symm_apply _ _⟩
  have he := count_erase_fixed_markers (Dart {e // selected e=true})
    (reversePerm {e // selected e=false}) (xs.map (partitionDartEquiv selected))
    (hn.map (partitionDartEquiv selected).injective) hmapfull
  rw [formPerm_fullContourWord C a hsingle] at ht
  rw [face_eq_contour_mul_visible]
  simp only [formPerm_eq_classical] at ht he ⊢
  exact ht.symm.trans he

 theorem visibleWord_partition_erase {E : Type*} (selected : E → Bool) (xs : List (Dart E)) :
    (visibleWord (xs.map (partitionDartEquiv selected))).map (fun a => (a.1.val,a.2))=
      xs.filter (fun a => !(selected a.1)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨e,b⟩
      cases he : selected e <;> simp_all [visibleWord,partitionDartEquiv]

 theorem visibleContourWord_erase {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a : Dart E) :
    (visibleContourWord rows.rotation selected a).map (fun a => (a.1.val,a.2))=
      contourPortWord rows selected a :=
  visibleWord_partition_erase selected _

 theorem count_faces_of_noncrossing {E : Type*} [Finite E] [DecidableEq E]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x)
    [Nonempty {e // selected e=false}]
    (horder : ∀e f : {e // selected e=false}, e≠f → PortNoncrossing
      ((visibleContourWord R selected a).idxOf (e,true)) ((visibleContourWord R selected a).idxOf (e,false))
      ((visibleContourWord R selected a).idxOf (f,true)) ((visibleContourWord R selected a).idxOf (f,false))) :
    count ((reversePerm E).trans R)=Nat.card {e // selected e=false}+1 := by
  rw [count_faces_eq_bouquet R selected a hsingle]
  let C := (partialReverse E selected).trans R
  have hn : ((orbitPrefix C (Function.minimalPeriod C a) a).map (partitionDartEquiv selected)).Nodup :=
    (orbitPrefix_nodup C a (le_refl _)).map (partitionDartEquiv selected).injective
  have hfull : ∀x,x∈(orbitPrefix C (Function.minimalPeriod C a) a).map (partitionDartEquiv selected) := by
    intro x
    exact List.mem_map.mpr ⟨(partitionDartEquiv selected).symm x,
      mem_fullContourWord C a _ hsingle,Equiv.apply_symm_apply _ _⟩
  apply NoncrossingBouquet.count_eq_card_add_one _ (visibleWord_nodup hn) (visibleWord_full hfull)
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using horder

 theorem count_faces_of_key_noncrossing {E K : Type*} [Finite E] [DecidableEq E] [LinearOrder K]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x)
    [Nonempty {e // selected e=false}]
    (key : Dart {e // selected e=false} → K)
    (hsort : (visibleContourWord R selected a).Pairwise (fun x y => key x<key y))
    (horder : ∀e f : {e // selected e=false}, e≠f →
      PortNoncrossing (key (e,true)) (key (e,false)) (key (f,true)) (key (f,false))) :
    count ((reversePerm E).trans R)=Nat.card {e // selected e=false}+1 := by
  apply count_faces_of_noncrossing R selected a hsingle
  intro e f hef
  exact PortNoncrossing.map_with key (fun x => (visibleContourWord R selected a).idxOf x)
    (fun {x y} hxy => sorted_key_idxOf_lt _ key hsort
      (visibleContourWord_full R selected a hsingle x)
      (visibleContourWord_full R selected a hsingle y) hxy) (horder e f hef)

 theorem count_faces_tree_only {E : Type*} [DecidableEq E]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x)
    (hall : ∀e,selected e=true) : count ((reversePerm E).trans R)=1 := by
  have hrev : partialReverse E selected=reversePerm E := by
    apply Equiv.ext
    intro x
    simp [partialReverse,hall]
  rw [hrev] at hsingle
  exact count_singleCycle _ a hsingle

end PlanarHom.PlanarityLRRealization
