import PlanarHom.NoncrossingBouquetDeletionCount
import Mathlib.Data.Fintype.Card

/-! NEW exact noncrossing bouquet face-cycle count by adjacent-pair deletion.
The empty dart permutation has zero literal cycles and is stated separately. -/
noncomputable section
universe u
namespace PlanarHom.NoncrossingBouquet
open MultiGraph.Kasteleyn FinitePermutationCycles PlanarityLRRealization
local instance bouquetCountBEq {F : Type*} [DecidableEq F] : BEq (Dart F) := instBEqOfDecidableEq
local instance bouquetCountLawfulBEq {F : Type*} [DecidableEq F] : LawfulBEq (Dart F) := by infer_instance

theorem full_word_length {E : Type*} [DecidableEq E] [Finite E]
    (word : List (Dart E)) (hn : word.Nodup) (hfull : ∀a,a∈word) :
    word.length=Nat.card (Dart E) := by
  classical
  letI := Fintype.ofFinite (Dart E)
  have hu : word.toFinset=Finset.univ := by ext a; simp [hfull a]
  rw [←List.toFinset_card_of_nodup hn,hu,Finset.card_univ,Nat.card_eq_fintype_card]

theorem eraseOccurrence_length {E : Type*} [DecidableEq E]
    (word : List (Dart E)) (hn : word.Nodup) (a : Dart E) (pre post : List (Dart E))
    (hw : word=pre++a::(a.1,!a.2)::post) :
    (eraseOccurrence a.1 word).length+2=word.length := by
  have hh:=congrArg List.length (eraseOccurrence_decomposition word hn a pre post hw)
  simp only [List.length_map,List.length_append] at hh
  have hwlen:=congrArg List.length hw
  simp only [List.length_append,List.length_cons] at hwlen
  omega

theorem pair_face_one {E : Type*} [DecidableEq E] (a : Dart E)
    (hfull : ∀x,x∈[a,(a.1,!a.2)]) :
    [a,(a.1,!a.2)].formPerm * reversePerm E=1 := by
  apply Equiv.ext
  intro x
  change [a,(a.1,!a.2)].formPerm (reversePerm E x)=x
  rw [List.formPerm_pair]
  have hm:=hfull x
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with hx | hx
  · rw [hx]
    change Equiv.swap a (a.1,!a.2) (a.1,!a.2)=a
    exact Equiv.swap_apply_right _ _
  · rw [hx]
    have hr : reversePerm E (a.1,!a.2)=a := by rcases a with ⟨e,b⟩; cases b <;> rfl
    rw [hr]
    exact Equiv.swap_apply_left _ _

theorem count_word_length_aux (n : ℕ) :
    ∀(E : Type u) [DecidableEq E] [Finite E] (word : List (Dart E)), word.Nodup → (∀a,a∈word) →
    (∀e f,e≠f→PortNoncrossing
      (word.idxOf (e,true)) (word.idxOf (e,false)) (word.idxOf (f,true)) (word.idxOf (f,false))) →
    word.length=n → word≠[] → count (word.formPerm * reversePerm E)=word.length/2+1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro E _ _ word hn hfull horder hlen hne
      classical
      obtain ⟨a₀,ha₀⟩:=List.exists_mem_of_ne_nil word hne
      letI : Nonempty E:=⟨a₀.1⟩
      obtain ⟨a,pre,post,hw⟩:=exists_adjacent_reverse_pair word hn hfull horder
      have hsize:=eraseOccurrence_length word hn a pre post hw
      by_cases hy : eraseOccurrence a.1 word=[]
      · have hp : pre=[] := by
          have hh:=congrArg List.length (eraseOccurrence_decomposition word hn a pre post hw)
          simp only [hy,List.map_nil,List.length_nil,List.length_append] at hh
          exact List.length_eq_zero_iff.mp (by omega)
        have hq : post=[] := by
          have hh:=congrArg List.length (eraseOccurrence_decomposition word hn a pre post hw)
          simp only [hy,List.map_nil,List.length_nil,List.length_append] at hh
          exact List.length_eq_zero_iff.mp (by omega)
        have hpair : word=[a,(a.1,!a.2)] := by simpa only [hp,hq,List.nil_append] using hw
        calc
          count (word.formPerm * reversePerm E)=Nat.card (Dart E) := by
            rw [hpair,pair_face_one a (fun x=>hpair ▸ hfull x),count_one]
          _=word.length := (full_word_length word hn hfull).symm
          _=word.length/2+1 := by rw [hpair]; norm_num
      · rw [count_delete_adjacent_pair word hn hfull a pre post hw hy]
        have hsmall : (eraseOccurrence a.1 word).length<n := by omega
        have hc:=ih _ hsmall {e:E // e≠a.1} (eraseOccurrence a.1 word)
          (eraseOccurrence_nodup a.1 word hn) (eraseOccurrence_full a.1 word hfull)
          (eraseOccurrence_noncrossing a.1 word hn hfull horder) rfl hy
        rw [hc]
        omega

/-- Every nonempty complete noncrossing occurrence bouquet has exactly one more
literal face cycle than edge occurrences. Fixed-point face cycles are included. -/
theorem count_eq_card_add_one {E : Type u} [DecidableEq E] [Finite E] [Nonempty E]
    (word : List (Dart E)) (hn : word.Nodup) (hfull : ∀a,a∈word)
    (horder : ∀e f,e≠f→PortNoncrossing
      (word.idxOf (e,true)) (word.idxOf (e,false)) (word.idxOf (f,true)) (word.idxOf (f,false))) :
    count (word.formPerm * reversePerm E)=Nat.card E+1 := by
  have hne : word≠[] := List.ne_nil_of_mem (hfull (Classical.choice inferInstance,true))
  rw [count_word_length_aux word.length E word hn hfull horder rfl hne,full_word_length word hn hfull]
  simp [Dart,Nat.card_prod,Nat.card_eq_fintype_card]

/-- An edgeless bouquet has no dart and no literal face-table cycle. -/
theorem count_empty_bouquet {E : Type*} [DecidableEq E] [IsEmpty E]
    (word : List (Dart E)) : count (word.formPerm * reversePerm E)=0 := count_empty _

end PlanarHom.NoncrossingBouquet
