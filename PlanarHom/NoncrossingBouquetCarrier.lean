import PlanarHom.NoncrossingBouquetErase
import PlanarHom.NoncrossingBouquetPairExtension
import PlanarHom.FinitePermutationCycleTransport

/-! NEW exact carrier equivalence after deleting one named occurrence pair. -/
noncomputable section
namespace PlanarHom.NoncrossingBouquet
open MultiGraph.Kasteleyn FinitePermutationCycles PlanarityLRRealization
variable {E : Type*} [DecidableEq E]

def restoreDart (a : Dart E) : TwoFresh (Dart {e:E // e≠a.1})→Dart E
  | .inl (.inl b)=>remainingLift a.1 b
  | .inl (.inr _)=>a
  | .inr _=>(a.1,!a.2)

def restrictDart (a b : Dart E) : TwoFresh (Dart {e:E // e≠a.1}) :=
  if h : b.1=a.1 then if b.2=a.2 then firstDart else secondDart
  else oldDart (⟨b.1,h⟩,b.2)

theorem restore_restrict (a b : Dart E) : restoreDart a (restrictDart a b)=b := by
  rcases a with ⟨e,u⟩
  rcases b with ⟨f,v⟩
  by_cases he : f=e
  · subst f
    cases u <;> cases v <;> simp [restrictDart,restoreDart,firstDart,secondDart]
  · simp [restrictDart,restoreDart,oldDart,remainingLift,he]

theorem restrict_restore (a : Dart E) (b : TwoFresh (Dart {e:E // e≠a.1})) :
    restrictDart a (restoreDart a b)=b := by
  rcases b with (b | u) | u
  · rcases b with ⟨e,bit⟩
    simp [restoreDart,remainingLift,restrictDart,e.property,oldDart]
  · cases u
    simp [restoreDart,restrictDart,firstDart]
  · cases u
    cases h:a.2 <;> simp [restoreDart,restrictDart,secondDart,h]

def dartPairEquiv (a : Dart E) : TwoFresh (Dart {e:E // e≠a.1}) ≃ Dart E where
  toFun := restoreDart a
  invFun := restrictDart a
  left_inv := restrict_restore a
  right_inv := restore_restrict a

@[simp] theorem dartPairEquiv_old (a : Dart E) (b : Dart {e:E // e≠a.1}) :
    dartPairEquiv a (oldDart b)=remainingLift a.1 b := rfl
@[simp] theorem dartPairEquiv_first (a : Dart E) : dartPairEquiv a firstDart=a := rfl
@[simp] theorem dartPairEquiv_second (a : Dart E) : dartPairEquiv a secondDart=(a.1,!a.2) := rfl

theorem dartPairEquiv_reverse (a : Dart E) (x : TwoFresh (Dart {e:E // e≠a.1})) :
    dartPairEquiv a (pairReverse (reversePerm _) x)=reversePerm E (dartPairEquiv a x) := by
  rcases x with (x | u) | u
  · change dartPairEquiv a (pairReverse (reversePerm _) (oldDart x))=_
    rw [pairReverse_old,dartPairEquiv_old]
    rfl
  · cases u
    change dartPairEquiv a (pairReverse (reversePerm _) firstDart)=_
    rw [pairReverse_first,dartPairEquiv_second]
    rfl
  · cases u
    change dartPairEquiv a (pairReverse (reversePerm _) secondDart)=_
    rw [pairReverse_second,dartPairEquiv_first]
    simp [reversePerm,dartPairEquiv,restoreDart]

theorem dartPairEquiv_pairWord (a : Dart E) (word : List (Dart {e:E // e≠a.1})) :
    (pairWord word).map (dartPairEquiv a)=a::(a.1,!a.2)::word.map (remainingLift a.1) := by
  simp only [pairWord,List.map_cons,List.map_map,Function.comp_def,dartPairEquiv_first,
    dartPairEquiv_second,dartPairEquiv_old]

theorem count_pairWord_transport [Finite E] (a : Dart E) (word : List (Dart {e:E // e≠a.1}))
    (hn : word.Nodup) (hfull : ∀b,b∈word) :
    count ((pairWord word).formPerm * pairReverse (reversePerm {e:E // e≠a.1}))=
      count ((a::(a.1,!a.2)::word.map (remainingLift a.1)).formPerm * reversePerm E) := by
  have hpfull : ∀x:TwoFresh (Dart {e:E // e≠a.1}),x∈pairWord word := by
    intro x
    rcases x with (x | u) | u
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x,hfull x,rfl⟩))
    · cases u; exact List.mem_cons_self ..
    · cases u; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  apply count_semiconj _ _ (dartPairEquiv a)
  intro x
  change dartPairEquiv a ((pairWord word).formPerm (pairReverse (reversePerm _) x))=
    (a::(a.1,!a.2)::word.map (remainingLift a.1)).formPerm (reversePerm E (dartPairEquiv a x))
  rw [←dartPairEquiv_reverse]
  have hh:=PlanarityLRRealization.map_formPerm_apply (dartPairEquiv a) (dartPairEquiv a).injective
    (pairWord word) (pairWord_nodup word hn) (hpfull (pairReverse (reversePerm _) x))
  rw [dartPairEquiv_pairWord] at hh
  exact hh.symm

end PlanarHom.NoncrossingBouquet
