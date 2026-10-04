import PlanarHom.NoncrossingBouquetAdjacentPair

/-! NEW literal occurrence deletion, preserving every other paired dart and its order. -/
noncomputable section
namespace PlanarHom.NoncrossingBouquet
open MultiGraph.Kasteleyn
variable {E : Type*} [DecidableEq E]
local instance bouquetEraseBEq {F : Type*} [DecidableEq F] : BEq (Dart F) := instBEqOfDecidableEq
local instance bouquetEraseLawfulBEq {F : Type*} [DecidableEq F] : LawfulBEq (Dart F) := by infer_instance

def remainingLift (e : E) (a : Dart {f:E // f≠e}) : Dart E := (a.1.val,a.2)

theorem remainingLift_injective (e : E) : Function.Injective (remainingLift e) := by
  intro a b h
  change (a.1.val,a.2)=(b.1.val,b.2) at h
  exact Prod.ext (Subtype.ext (congrArg (fun p:Dart E=>p.1) h)) (congrArg (fun p:Dart E=>p.2) h)

def eraseOccurrence (e : E) (word : List (Dart E)) : List (Dart {f:E // f≠e}) :=
  (word.filter (fun a=>decide (a.1≠e))).attach.map (fun a=>
    ((⟨a.val.1,by
      have hh : decide (a.val.1≠e)=true := (List.mem_filter.mp a.property).2
      exact of_decide_eq_true hh⟩ : {f:E // f≠e}),a.val.2))

theorem eraseOccurrence_map (e : E) (word : List (Dart E)) :
    (eraseOccurrence e word).map (remainingLift e)=word.filter (fun a=>decide (a.1≠e)) := by
  simp only [eraseOccurrence,List.map_map,Function.comp_def,remainingLift,Prod.mk.eta,List.attach_map_subtype_val]

theorem eraseOccurrence_nodup (e : E) (word : List (Dart E)) (hn : word.Nodup) :
    (eraseOccurrence e word).Nodup := by
  apply List.Nodup.of_map (remainingLift e)
  rw [eraseOccurrence_map]
  exact hn.filter _

theorem eraseOccurrence_full (e : E) (word : List (Dart E)) (hfull : ∀a,a∈word)
    (a : Dart {f:E // f≠e}) : a∈eraseOccurrence e word := by
  have hm : remainingLift e a∈(eraseOccurrence e word).map (remainingLift e) := by
    rw [eraseOccurrence_map]
    exact List.mem_filter.mpr ⟨hfull _,decide_eq_true a.1.property⟩
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hm
  exact (remainingLift_injective e he) ▸ hb

theorem eraseOccurrence_noncrossing (e : E) (word : List (Dart E)) (hn : word.Nodup)
    (hfull : ∀a,a∈word)
    (horder : ∀e f,e≠f→PortNoncrossing
      (word.idxOf (e,true)) (word.idxOf (e,false)) (word.idxOf (f,true)) (word.idxOf (f,false))) :
    ∀f k : {f:E // f≠e},f≠k→PortNoncrossing
      ((eraseOccurrence e word).idxOf (f,true)) ((eraseOccurrence e word).idxOf (f,false))
      ((eraseOccurrence e word).idxOf (k,true)) ((eraseOccurrence e word).idxOf (k,false)) := by
  have hs : word.Pairwise (fun a b=>word.idxOf a<word.idxOf b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.idxOf_getElem hn] using hij
  have hm : ((eraseOccurrence e word).map (remainingLift e)).Sublist word := by
    rw [eraseOccurrence_map]
    exact List.filter_sublist
  have hsort := hs.sublist hm
  rw [List.pairwise_map] at hsort
  intro f k hfk
  have hne : f.val≠k.val := fun h=>hfk (Subtype.ext h)
  exact PortNoncrossing.map_with (fun a:Dart {f:E // f≠e}=>word.idxOf (remainingLift e a))
    (fun a=>(eraseOccurrence e word).idxOf a)
    (fun {a b} h=>sorted_key_idxOf_lt _ _ hsort
      (eraseOccurrence_full e word hfull a) (eraseOccurrence_full e word hfull b) h)
    (a:=(f,true)) (b:=(f,false)) (c:=(k,true)) (d:=(k,false)) (horder f.val k.val hne)

theorem dart_eq_or_reverse (a b : Dart E) (h : b.1=a.1) : b=a ∨ b=(a.1,!a.2) := by
  rcases a with ⟨e,x⟩
  rcases b with ⟨f,y⟩
  dsimp at h
  subst f
  cases x <;> cases y <;> simp

theorem eraseOccurrence_decomposition (word : List (Dart E)) (hn : word.Nodup)
    (a : Dart E) (pre post : List (Dart E)) (hw : word=pre++a::(a.1,!a.2)::post) :
    (eraseOccurrence a.1 word).map (remainingLift a.1)=pre++post := by
  rw [eraseOccurrence_map,hw]
  have hnd : (pre++a::(a.1,!a.2)::post).Nodup := hw ▸ hn
  have hsep := (List.nodup_append.mp hnd).2.2
  have htail := (List.nodup_append.mp hnd).2.1
  have hp : pre.filter (fun b=>decide (b.1≠a.1))=pre := by
    apply List.filter_eq_self.mpr
    intro b hb
    apply decide_eq_true
    intro h
    rcases dart_eq_or_reverse a b h with he | he
    · exact hsep b hb a (by simp) he
    · exact hsep b hb (a.1,!a.2) (by simp) he
  have hq : post.filter (fun b=>decide (b.1≠a.1))=post := by
    apply List.filter_eq_self.mpr
    intro b hb
    apply decide_eq_true
    intro h
    rcases dart_eq_or_reverse a b h with he | he
    · exact (List.nodup_cons.mp htail).1 (List.mem_cons_of_mem _ (he ▸ hb))
    · exact (List.nodup_cons.mp (List.nodup_cons.mp htail).2).1 (he ▸ hb)
  simp only [List.filter_append,hp,List.filter_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false,hq]

end PlanarHom.NoncrossingBouquet
