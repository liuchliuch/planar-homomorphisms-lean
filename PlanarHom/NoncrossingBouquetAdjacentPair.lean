import PlanarHom.OrderedPortTransport
import PlanarHom.PlanarityLRContourPermutation
import Mathlib.GroupTheory.Perm.List

/-! NEW adjacent reverse-pair existence from the actual noncrossing port ranks. -/
noncomputable section
namespace PlanarHom.NoncrossingBouquet
open MultiGraph.Kasteleyn
variable {E : Type*} [DecidableEq E]
local instance bouquetAdjacentBEq : BEq (Dart E) := instBEqOfDecidableEq
local instance bouquetAdjacentLawfulBEq : LawfulBEq (Dart E) := by infer_instance

def lowerRank (word : List (Dart E)) (e : E) : ℕ := min (word.idxOf (e,true)) (word.idxOf (e,false))
def upperRank (word : List (Dart E)) (e : E) : ℕ := max (word.idxOf (e,true)) (word.idxOf (e,false))

theorem endpoint_rank (word : List (Dart E)) (e : E) (b : Bool) :
    word.idxOf (e,b)=lowerRank word e ∨ word.idxOf (e,b)=upperRank word e := by
  unfold lowerRank upperRank
  rcases le_total (word.idxOf (e,true)) (word.idxOf (e,false)) with h | h
  · rw [min_eq_left h,max_eq_right h]
    cases b <;> simp
  · rw [min_eq_right h,max_eq_left h]
    cases b <;> simp

theorem lowerRank_lt_upperRank (word : List (Dart E))
    (hfull : ∀a,a∈word) (e : E) : lowerRank word e<upperRank word e := by
  have hn : word.idxOf (e,true)≠word.idxOf (e,false) := by
    intro he
    have hh := (List.idxOf_inj (hfull (e,true)) (hfull (e,false))).mp he
    cases congrArg Prod.snd hh
  unfold lowerRank upperRank
  rcases lt_or_gt_of_ne hn with h | h
  · simpa only [min_eq_left h.le,max_eq_right h.le] using h
  · simpa only [min_eq_right h.le,max_eq_left h.le] using h

theorem upperRank_lt_length (word : List (Dart E)) (hfull : ∀a,a∈word) (e : E) :
    upperRank word e<word.length :=
  max_lt (List.idxOf_lt_length_iff.mpr (hfull (e,true))) (List.idxOf_lt_length_iff.mpr (hfull (e,false)))

theorem exists_adjacent_rank_pair [Nonempty E] (word : List (Dart E)) (hn : word.Nodup)
    (hfull : ∀a,a∈word)
    (horder : ∀e f,e≠f→PortNoncrossing
      (word.idxOf (e,true)) (word.idxOf (e,false)) (word.idxOf (f,true)) (word.idxOf (f,false))) :
    ∃e,upperRank word e=lowerRank word e+1 := by
  classical
  let gap := fun e=>upperRank word e-lowerRank word e
  have hex : ∃n,∃e,gap e=n := ⟨gap (Classical.choice inferInstance),Classical.choice inferInstance,rfl⟩
  obtain ⟨e,he⟩ := Nat.find_spec hex
  have hmin : ∀f,gap e≤gap f := by
    intro f
    rw [he]
    exact Nat.find_min' hex ⟨f,rfl⟩
  refine ⟨e,?_⟩
  have hle := lowerRank_lt_upperRank word hfull e
  by_contra hnot
  have hgap : lowerRank word e+1<upperRank word e := by omega
  have hlen : lowerRank word e+1<word.length := hgap.trans (upperRank_lt_length word hfull e)
  let a := word[lowerRank word e+1]
  have har : word.idxOf a=lowerRank word e+1 := List.idxOf_getElem hn _ hlen
  have haf : word.idxOf a=lowerRank word a.1 ∨ word.idxOf a=upperRank word a.1 := endpoint_rank word a.1 a.2
  have hne : e≠a.1 := by
    intro hh
    rw [←hh] at haf
    omega
  have ho := horder e a.1 hne
  change upperRank word e<lowerRank word a.1 ∨ upperRank word a.1<lowerRank word e ∨
    (lowerRank word e<lowerRank word a.1 ∧ upperRank word a.1<upperRank word e) ∨
    (lowerRank word a.1<lowerRank word e ∧ upperRank word e<upperRank word a.1) at ho
  have hfle := lowerRank_lt_upperRank word hfull a.1
  have hm := hmin a.1
  change upperRank word e-lowerRank word e≤upperRank word a.1-lowerRank word a.1 at hm
  rcases ho with h | h | h | h <;> omega


theorem adjacent_decomposition (word : List (Dart E)) (a b : Dart E)
    (ha : a∈word) (hb : b∈word) (hab : word.idxOf b=word.idxOf a+1) :
    ∃pre post,word=pre++a::b::post := by
  have hi:=List.idxOf_lt_length_iff.mpr ha
  have hj:=List.idxOf_lt_length_iff.mpr hb
  have hij : word.idxOf a+1<word.length := by omega
  have hga:=List.getElem_idxOf hi
  have hgb : word[word.idxOf a+1]=b := by simpa only [hab] using List.getElem_idxOf hj
  refine ⟨word.take (word.idxOf a),word.drop (word.idxOf a+1+1),?_⟩
  calc
    word=word.take (word.idxOf a)++word.drop (word.idxOf a) := (List.take_append_drop _ _).symm
    _=_ := by rw [List.drop_eq_getElem_cons hi,List.drop_eq_getElem_cons hij,hga,hgb]

theorem exists_adjacent_reverse_pair [Nonempty E] (word : List (Dart E)) (hn : word.Nodup)
    (hfull : ∀a,a∈word)
    (horder : ∀e f,e≠f→PortNoncrossing
      (word.idxOf (e,true)) (word.idxOf (e,false)) (word.idxOf (f,true)) (word.idxOf (f,false))) :
    ∃a pre post,word=pre++a::(a.1,!a.2)::post := by
  obtain ⟨e,he⟩:=exists_adjacent_rank_pair word hn hfull horder
  rcases le_total (word.idxOf (e,true)) (word.idxOf (e,false)) with h | h
  · simp only [lowerRank,upperRank,min_eq_left h,max_eq_right h] at he
    obtain ⟨pre,post,hh⟩:=adjacent_decomposition word (e,true) (e,false) (hfull _) (hfull _) he
    exact ⟨(e,true),pre,post,hh⟩
  · simp only [lowerRank,upperRank,min_eq_right h,max_eq_left h] at he
    obtain ⟨pre,post,hh⟩:=adjacent_decomposition word (e,false) (e,true) (hfull _) (hfull _) he
    exact ⟨(e,false),pre,post,hh⟩

end PlanarHom.NoncrossingBouquet
